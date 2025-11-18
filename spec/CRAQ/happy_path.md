# CRAQ in 3FS – Happy Path

This document captures the happy-path behavior of the 3FS CRAQ-based storage replication, focusing on read/write consistency at the chunk level without failures.

## Entities
- **Client**: Issues read and write requests on file chunks.
- **MetaService / Layout**: Maps files → chunks → chains (head, middle, tail) and provides `VersionedChainId`.
- **StorageClient**: Uses routing info + chain layout to send operations to storage targets.
- **StorageTarget**: Physical storage server hosting chunk replicas in a chain.
- **ChunkReplica**: Per-chunk state on a storage target: committed version, optional pending version, data.
- **ReliableUpdate**: Per-target component that serializes updates on a chunk using locks and versioning.
- **ReliableForwarding**: Forwards update operations along the chain (head→…→tail) with retries.
- **LockManager**: Provides per-chunk locks to serialize writes at the head.
- **ResyncWorker**: Not used in happy path; handles recovery in failure scenarios.

## State / Data
At a high level, for each chunk:
- `version` $v \in \mathbb{N}$: committed version, monotonically increasing.
- `pendingVersion` $u$ (optional): if present, $u = v + 1$ while a write is in flight.
- `data[v]`: committed data for version $v$.
- `data[u]`: pending data for in-flight write.

For a chain:
- `Chain = [t_0, t_1, ..., t_{n-1}]` where `t_0` is head, `t_{n-1}` is tail.
- `chainVersion` $cv$: configuration version for this chain.

## Happy Path Write Workflow

Assume no failures, correct routing info, and a single chain per chunk.

1. **Client issues write**
   - Client calls `StorageClient::write(...)` for chunk `c` on chain `C`.
   - StorageClient selects chain and obtains `VersionedChainId` $(chainId, chainVer)$.

2. **Head receives write**
   - Head target validates routing: request carries `chainVer` matching its local chain version for `C`.
   - Head calls `ReliableUpdate` for chunk `c`.

3. **Head acquires lock & creates pending version**
   - `LockManager` acquires a lock for chunk `c`; concurrent writes to `c` are blocked.
   - Let current committed version be $v$; `ReliableUpdate` allocates pending version $u = v+1` and writes new data to `data[u]`.

4. **Head forwards write**
   - `ReliableForwarding` forwards the update (chunk id, `u`, data, `chainVer`) to the successor in the chain, preserving order.

5. **Intermediate nodes process write**
   - Each intermediate target $t_i$ ($0 < i < n-1$):
     - Validates `chainVer`.
     - Creates pending version $u = v+1$ for chunk `c` (with same version number as upstream).
     - Forwards the update to successor $t_{i+1}$.

6. **Tail commits**
   - Tail target $t_{n-1}$:
     - Validates `chainVer` and per-chunk ordering.
     - Atomically replaces `committed` from version $v$ to $u$ and marks `pendingVersion` consumed.
     - Sends an acknowledgment back to its predecessor.

7. **Back-propagated commit**
   - Each predecessor, upon receiving ack from successor:
     - Commits chunk `c` from `v` to `u`.
     - Forwards ack towards head.

8. **Head completes write**
   - Head commits `v → u`.
   - Releases the chunk lock.
   - Responds `success` to the client.

**Happy-path guarantee:** On success, all replicas on the chain have committed version $u = v+1$ with identical data.

## Happy Path Read Workflow

Assume only committed data or, when there is a concurrent write, that the read is either:
- Strict (must see last committed) or
- Relaxed (may read pending).

1. **Client issues read**
   - Client calls `StorageClient::read(...)` for chunk `c`, using current `VersionedChainId`.
   - Read is routed to one of the chain replicas according to CRAQ policy (e.g., head, tail, or middle based on load).

2. **Target serves read**
   - Target checks chunk state:
     - If only a committed version $v$ exists, it returns `data[v]`.
     - If $v$ and a pending $u = v+1$ exist:
       - For strict read: returns `data[v]` or a special status indicating that a newer pending version exists (client may retry).
       - For relaxed read: client may explicitly request pending data `data[u]`.

3. **Client consistency**
   - Clients that only perform strict reads and write-complete operations observe a linearizable history: once a write completes, all subsequent strict reads of that chunk return the new committed version.

## Success Conditions

- **Write-complete:** Any write that returns success from `StorageClient` has been committed at tail, and all replicas hold the same committed version for the updated chunk.
- **Monotone versions:** For each chunk replica, its committed version number is monotonically increasing over time.
- **Read-after-write:** For a single client, a strict read issued after a completed write to the same chunk returns at least that committed version.
- **No torn reads:** Reads never see a mixture of old and new data for a single chunk version.

These form the baseline behaviors that the TLA+ model will capture before adding failures and rebuild behavior.
