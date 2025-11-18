# CRAQ – Behavioral Diagrams

This document sketches key interaction/state diagrams for CRAQ in 3FS, focusing on consistency across failures and rebuild.

## 1. Happy Path Write and Read (Single Chain)

Textual summary (corresponds to standard chain replication with CRAQ reads):

- Write: `Client → Head → ... → Tail → ... → Head → Client`.
- Read (strict): `Client → any serving target → committed version`.
- Read (relaxed): `Client → target with pending/committed → pending or committed version (by mode)`.

## 2. Middle Target Failure During Write

Scenario: chain `[A, B, C]` with `B` failing during write.

Sequence outline:

1. Client sends `Write(x, data)` to `A` with `(chainId, chainVer=v)`.
2. `A` locks chunk `x`, creates pending `u = v+1`, forwards to `B`.
3. `B` fails (crash) before commit.
4. Mgmtd detects heartbeat failure, marks `B` offline, increments chain version to `v'`, updates chain to `[A, C, B]`.
5. `A`'s request to `B` times out; it receives new routing with `v'`.
6. `A` re-sends write to `C` using `v'`.
7. `C` processes write, commits `u`, sends ack back to `A`.
8. `A` commits `u`, unlocks, replies success to client.

During steps 3–8:
- `B`'s state (if any pending) is not visible; it is `offline`.
- Reads are only sent to `A` or `C`.

## 3. Tail Failure During Write

Sequence outline:

1. `A` forwards write to `B`, then to `C`.
2. `C` fails before or just after commit.
3. Mgmtd detects failure, marks `C` offline, increments chain version and reconfigures chain.
4. `A` times out waiting for ack, observes new routing.
5. `A` retries the write to the new tail (which may be `B` or some other successor) using the same write id and version.
6. New tail commits and acks; `A` commits and responds to client.

## 4. Target Rebuild (Resync)

Sequence outline:

1. Target `T` restarts and registers with Mgmtd.
2. Mgmtd inserts `T` at tail of chain and marks state `waiting`.
3. Mgmtd transitions `T` to `syncing` and triggers `ResyncWorker` on predecessor `P`.
4. `P` requests chunk metadata from `T`.
5. For each chunk where `commitVersion(P) > commitVersion(T)` or inconsistent:
   - `P` locks chunk.
   - `P` sends full-chunk-replace write to `T`.
   - `T` updates its committed state and acks.
   - `P` unlocks chunk.
6. After all chunks are synchronized, `P` sends `SyncDone` to `T`.
7. `T` reports `up-to-date`; Mgmtd marks `T` as `serving` and updates routing.

## 5. State Machine Sketches

We will capture these in TLA+ rather than full diagram syntax, but conceptually:

### 5.1 Target State (Per Chain)

States: `offline`, `waiting`, `syncing`, `serving`, `lastsrv`.

Transitions (simplified):

- `offline → waiting` (on restart & registration).
- `waiting → syncing` (when resync starts).
- `syncing → serving` (when sync completed and reported).
- `serving → offline` (on heartbeat failure/crash).
- `serving → lastsrv` (special case when all other targets fail).

### 5.2 Per-Chunk Version State on a Target

Variables (per chunk):
- `committedVersion` (Nat).
- `pendingVersion` (Nat ∪ {None}).

Operations:
- `StartWrite(u)`: requires `pendingVersion = None` and `u = committedVersion + 1`; sets `pendingVersion := u`.
- `CommitPending()`: requires `pendingVersion ≠ None`; sets `committedVersion := pendingVersion; pendingVersion := None`.
- `AbortPending()`: sets `pendingVersion := None` without changing `committedVersion`.
- `SyncFromPredecessor(w)`: sets `committedVersion := w.version`, `pendingVersion := None`.

These textual diagrams will guide how we structure the TLA+ `Next` relation.
