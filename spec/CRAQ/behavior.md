# CRAQ – Error Handling and Concurrency Behavior

This document captures CRAQ behavior in 3FS under failures, retries, and concurrent operations, focusing on consistency between reads and writes during storage target failure and rebuild.

## 1. Failure Modes

We consider a single chain `C` with members `[A, B, C]` (head→tail) and focus on these failures:

1. **Middle target failure during write**
   - Write is in-flight from `A` to `B` (or `B` to `C`).
   - `B` crashes before committing or forwarding.

2. **Tail failure during write**
   - `C` crashes after receiving pending version but before committing or acknowledging.

3. **Head failure during write**
   - `A` crashes after creating pending version locally, possibly after forwarding.

4. **Target failure outside writes**
   - Target fails when idle / only serving reads.

5. **Recovery / rebuild**
   - Failed target restarts and must be resynchronized before rejoining as `serving`.

## 2. Error Handling – Chain Reconfiguration

### 2.1 Failure Detection

- Mgmtd periodically sends/receives heartbeats to/from storage targets.
- On missed heartbeats for a threshold, it marks the target `offline` and increments the **chain version** for any affected chain.

### 2.2 Chain Versioning and Routing

- Each chain `C` is identified by `(chainId, chainVer)`.
- Mgmtd updates routing tables with a new chain version when it removes or reorders targets.
- Updated routing info (including `chainVer`) is broadcast to clients and storage services.
- StorageClient and StorageService validate chain version in requests; mismatches cause `RoutingVersionMismatch` errors and retries using updated routing.

### 2.3 Reconfiguring the Chain

- When a target `T` in chain `[A, B, C]` fails:
  - `T` is moved to the end of the chain as `offline`.
  - Example: `B` fails → chain becomes `[A, C, B]` with new `chainVer`.
- Clients and storage targets only treat `serving` members at the front of the chain as active for new operations; `waiting`/`syncing`/`offline` members are skipped.

## 3. Error Handling – Write Protocol Under Failure

### 3.1 Head’s Perspective

- Head `A` serializes writes per chunk via locks.
- For a write on chunk `x`:
  1. Acquire lock for `x`; create pending version `u = v+1` locally.
  2. Forward to successor.
  3. Wait for acknowledgment from tail or timeout.

- If forwarding to successor fails or times out:
  - Head checks for updated routing / chain version.
  - If chain version changed, head retries forwarding to the new successor using `ReliableForwarding`.
  - Head keeps the lock until the write either commits or is aborted.

### 3.2 Middle Target Failure During Write

Scenario: chain `[A(head), B, C(tail)]`; `B` fails during write.

- Write path before failure:
  - `A` has pending `u` and forwards to `B`.
  - `B` may or may not have created its own pending before failing.
- Failure handling:
  - Heartbeats mark `B` as `offline`; chain version increments; new chain `[A, C, B]` is broadcast.
  - `A`’s in-flight request to `B` times out.
  - `A` observes chain version update and re-sends the same write to new successor `C` with higher `chainVer` and the same version `u`.
  - `C` processes the write and becomes tail; commits `u` and sends ack back to `A`.
  - `A` commits `u`, releases lock, and replies success.

**Consistency outcome:**
- Any local pending version on `B` is ignored while `B` is `offline`.
- Committed state after success: `A` and `C` have committed version `u`, `B` is out of the chain (offline / not serving). Reads only go to serving targets, so no client sees `B`’s stale/pending state.

### 3.3 Tail Failure During Write

Scenario: `C` fails after receiving write.

- If `C` fails before commit:
  - No ack is sent; `A`’s write eventually times out.
  - Mgmtd reconfigures chain to remove `C` (e.g., `[A, B]` or `[A, B, C]` with `C` moved to end and not serving).
  - Head re-sends write to new tail using updated chain version.
  - Pending versions on failed `C` are irrelevant while `C` is `offline`.

- If `C` fails after commit but before ack reaches `A`:
  - Depending on the implementation, the protocol ensures that **either**:
    - Ack was persisted or will be retried, eventually leading to commit at predecessors, or
    - The write is retried and idempotent; duplicates are detected via request IDs.
  - In all cases, `ReliableUpdate` and `ReliableForwarding` ensure no partial commit is externally visible: a write that returns success has consistent committed state on serving replicas.

### 3.4 Head Failure During Write

- If head fails after creating pending but before forwarding:
  - Pending state exists only on head (now `offline`).
  - No ack can have been sent; clients see failure or timeout and will retry via StorageClient once routing updates.

- Recovery paths:
  - If head is replaced/reconfigured (new head): new writes use the new chain; old head’s state is reconciled via rebuild if it re-enters the chain.
  - If the failed head’s pending version was never committed on any serving member, the write either never completes or is reissued, and only one successful completion is allowed due to idempotency.

## 4. Recovery and Rebuild – ResyncWorker

When a failed target `T` restarts:

1. **Registration and initial state**
   - `T` registers with Mgmtd and obtains current chain tables.
   - Mgmtd sets `T`’s public state to `waiting` and places it at the tail of the chain (e.g., `[A, C, T]`).
   - `T` does not serve client reads or writes in `waiting` state.

2. **Syncing state**
   - Mgmtd transitions `T` to `syncing` and triggers `ResyncWorker` on the predecessor (e.g., `C`).
   - `ResyncWorker` performs:
     - `DumpChunkMeta` from `T` → obtains metadata about chunks and versions on `T`.
     - For each chunk where `T` is missing data or has older / inconsistent version:
       - Predecessor acquires lock for that chunk.
       - Sends **full-chunk-replace write** with the current committed data and version.
       - Waits for ack from `T` and then releases lock.
   - The synchronization is version-aware: only chunks with `commitVersion(pred) > commitVersion(T)` or mismatched metadata are updated.

3. **Completion and serving state**
   - After sync, predecessor sends `SyncDone`.
   - `T` reports `up-to-date` in heartbeat; Mgmtd marks `T` as `serving`.
   - Updated routing/chain with `T` as a serving member is broadcast.

**Consistency outcome:**
- Before `T` is `serving`, any stale or partial state on it is not visible to clients.
- After sync, `T`’s committed state matches its predecessor’s committed state per chunk.

## 5. Concurrency Behavior

### 5.1 Concurrent Writes to Same Chunk

- Writes to the same chunk are serialized at the head by a per-chunk lock.
- Within a chain, per-chunk version numbers strictly increase.
- Duplicate or retried writes (due to timeouts or routing version mismatches) are deduplicated via request IDs, ensuring idempotence.

**Invariant idea:** For each chain and chunk, there is a total order of successful writes defined by their committed version numbers.

### 5.2 Concurrent Reads and Writes

- Reads may be placed on any `serving` target in the chain.
- When there is an in-flight write on chunk `x` with pending version `u = v+1`:
  - Targets that only have committed `v` respond with `data[v]`.
  - Targets that have both `v` and `u` respond:
    - For strict reads: `data[v]` or a status indicating pending `u` exists; client may retry.
    - For relaxed reads: `data[u]` if requested.

**Key behavior:**
- Strict reads on serving targets never return uncommitted data.
- Relaxed reads may see pending data but only from targets where the pending version is at least as new as any committed version.

### 5.3 Reads During Failure and Rebuild

- When a target fails and is marked `offline`, it is removed from the `serving` set; clients do not read from it.
- During rebuild (`waiting` or `syncing` state), the recovering target does not receive client reads or writes.
- After rebuild, when `T` becomes `serving`, its committed state is aligned with predecessor, so reads from `T` are consistent.

**Scenarios of interest:**
1. **Read-after-write with middle failure:**
   - Client writes `w1` to chunk `x` while middle fails.
   - After write completes successfully, any strict read from any serving target returns at least `w1`.

2. **Read-after-write with rebuild:**
   - Client writes `w1` while some target is offline.
   - Target rebuilds via `ResyncWorker` and becomes serving.
   - Strict reads from the rebuilt target return at least `w1`.

## 6. Candidate Invariants and Properties (Informal)

The behaviors above suggest the following properties to formalize:

1. **Safety – No stale reads from serving targets**
   - For any completed write `w` on chunk `x` with version `u`, any strict read from a `serving` target after `w` completes never returns a version `< u`.

2. **Safety – Monotone chain versions**
   - Chain versions never decrease; reconfiguration only increases `chainVer`.

3. **Safety – Serving implies up-to-date**
   - If a target is `serving` in routing info for chain `C`, then for every chunk replicated on `C`, its committed version is at least the predecessor’s committed version.

4. **Safety – Offline/Waiting/Syncing isolation**
   - Clients never send read/write requests to targets in `offline`, `waiting`, or `syncing` state.

5. **Safety – Single commit per version per chunk per target**
   - Each chunk version is committed at most once per target; duplicates are idempotent.

6. **Liveness – Write completion under bounded failures**
   - Under assumptions about stable head and at least one serving tail, a client write eventually either fails definitively or completes and becomes visible to strict reads.

These will be refined and formalized in `properties.md` and the TLA+ model.
