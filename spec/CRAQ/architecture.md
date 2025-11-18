# CRAQ in 3FS – Architecture Overview

This document summarizes the main components, data structures, and interfaces involved in CRAQ-based replication in 3FS, with a focus on consistency between reads and writes, including during target failure and rebuild.

## Components

- **Client** (`src/client/storage`)
  - Issues read/write/delete operations for chunks/files.
  - Maintains routing info (`RoutingInfoVersion`) and chain layout (`VersionedChainId`).

- **MetaService / Layout** (`src/meta`, `src/tools/commands/Layout.*`)
  - Maps file paths to layouts (chains and chunk placement).
  - Exposes chain id and chain version to clients.

- **Mgmtd (Cluster Manager)** (`src/mgmtd`)
  - Tracks nodes and storage targets, their states (serving, waiting, syncing, offline, lastsrv).
  - Detects failures via heartbeats and updates routing/chain tables.
  - Increments chain versions when configuration changes.

- **StorageService / StorageServer / StorageOperator** (`src/storage/service`)
  - Frontend for storage targets; receives RPCs from StorageClient.
  - `StorageOperator` coordinates updates, forwarding, and chain-aware request handling.

- **StorageTarget / ChunkReplica / ChunkStore** (`src/storage/store`)
  - `StorageTarget` represents a physical target; hosts multiple `ChunkReplica`s.
  - `ChunkReplica` maintains committed and pending versions for each chunk.

- **ReliableUpdate** (`src/storage/service/ReliableUpdate.*`)
  - Serializes updates per chunk via locks.
  - Manages creation and commit of pending versions.

- **ReliableForwarding** (`src/storage/service/ReliableForwarding.*`)
  - Forwards update operations along the chain with retry logic.
  - Ensures ordering consistent with CRAQ and chain replication.

- **ResyncWorker** (`src/storage/sync/ResyncWorker.*`)
  - Handles synchronization of recovering targets (state "syncing").
  - Pulls metadata and full-chunk-replace writes from a predecessor.

- **TargetMap / RoutingInfo** (`src/storage/service/TargetMap.*`, `src/mgmtd/service/RoutingInfo.*`)
  - Maintains in-memory mapping of chains, chain versions, and target states on each node.

## Data Structures (Conceptual)

We abstract the key state relevant to consistency:

- **Per-Chunk State on a Target**
  - `committedVersion : Nat` (monotone per chunk).
  - `pendingVersion : Nat ∪ {None}` (if present, must equal `committedVersion + 1`).
  - `committedData : Data` and `pendingData : Data`.

- **Chain Configuration**
  - `ChainId` identifies a logical chain.
  - `ChainVersion : Nat` monotonically increases on reconfiguration.
  - `ChainMembers : Seq<TargetId>` ordered from head to tail.
  - `TargetState ∈ {serving, waiting, syncing, offline, lastsrv}`.

- **Routing Info at Client / Target**
  - `RoutingInfoVersion : Nat` for the whole routing table.
  - Mapping `ChainId → (ChainVersion, ChainMembers, TargetStates)`.

## Interfaces and Protocols

- **Client → StorageService**
  - `Write(VersionedChainId, ChunkId, Data)`
  - `Read(VersionedChainId, ChunkId, mode)` where `mode ∈ {strict, relaxed}`.

- **StorageService (head) → StorageService (successor)**
  - Forwarded updates with chunk id, data, chain id, chain version, and write metadata.

- **StorageService ↔ Mgmtd**
  - Heartbeats with current target state.
  - Routing/chain table updates when chain version changes.

- **ResyncWorker (predecessor) → Recovering Target**
  - `DumpChunkMeta`, `FullChunkReplaceWrite`, `SyncDone`.

## Configuration & Parameters

- Chain length (commonly 3 targets in examples).
- Timeouts for detecting failed successors and for resync.
- Policy for read placement (head/tail/any) and relaxed vs strict reads.

## Simplifications for TLA+ Model

For the TLA+ spec we will:
- Model a single chain of fixed length (2–3 targets) to capture CRAQ semantics.
- Treat data as abstract values (e.g., integers) and focus on version ordering and visibility.
- Model routing and chain versions abstractly as part of each request.
- Include a simplified failure/rebuild protocol:
  - Targets can fail and recover.
  - On recovery, the target enters `syncing` and copies committed state from its predecessor before becoming `serving`.

These abstractions will preserve the core consistency behavior we want to verify while keeping the state space manageable.
