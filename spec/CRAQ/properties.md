# CRAQ – Verification Properties

This document lists the safety and liveness properties we will verify for CRAQ in 3FS using TLA+. Each property is given in natural language and then in semi-formal temporal logic notation.

We consider:
- A single chain `Chain` of length 2–3 with targets `T ∈ Targets`.
- Chunks `x ∈ Chunks` with versions `v ∈ Nat`.
- Target states `state[T] ∈ {offline, waiting, syncing, serving, lastsrv}`.
- Per-target, per-chunk committed version `committed[T,x]` and optional pending version `pending[T,x]`.
- A distinguished client that issues writes and strict reads.

We focus on strict reads for strong consistency; relaxed reads are allowed to return pending data but must not violate basic ordering.

Let `CompletedWrite(x,v)` be an abstract event meaning: a client write on chunk `x` has committed with version `v` and the client has received success.
Let `StrictReadResult(T,x,v)` mean: client performs a strict read from target `T` on chunk `x` and obtains version `v`.

## 1. Safety: No Stale Strict Reads from Serving Targets

**Informal:** Once a write on chunk `x` with version `v` has completed, any subsequent strict read from any `serving` target returns a version `≥ v`.

**Motivation:** Ensures read-after-write consistency across the chain, including during failures and after rebuild.

**Semi-formal property:** For all chunks `x` and versions `v`:

- `□ ( CompletedWrite(x,v) ⇒  □_{future} ( ∀ T ∈ Targets : (state[T] = serving ∧ StrictReadResult(T,x,v') ) ⇒ v' ≥ v ) )`

Where `□_{future}` means "from that point onward".

## 2. Safety: Serving Targets Are Up-to-Date (Per-Predecessor)

**Informal:** At all times, for any serving target `T` that has a predecessor `P` in the chain, `T`'s committed version for any chunk is at least `P`'s committed version (no serving node lags behind its predecessor).

**Semi-formal property:** For all time:

- `□ ( ∀ x ∈ Chunks, ∀ T,P ∈ Targets : Predecessor(P,T) ∧ state[T] = serving ∧ state[P] = serving ⇒ committed[T,x] ≥ committed[P,x] )`

This uses a static relation `Predecessor(P,T)` according to the current chain order.

## 3. Safety: Offline/Waiting/Syncing Isolation

**Informal:** Clients never send reads or writes to targets that are not in `serving` or `lastsrv` state.

**Semi-formal property:** For all time:

- `□ ( ∀ T ∈ Targets, x ∈ Chunks : (RequestToClient(T,x) ⇒ state[T] ∈ {serving, lastsrv}) )`

In the TLA+ model we will encode client actions so that requests are only issued to allowed targets; the property is then trivially ensured by construction but still serves as a sanity check.

## 4. Safety: Monotone Per-Chunk Version Numbers

**Informal:** For each target and chunk, the committed version is monotonically increasing, and the pending version (if present) is either `None` or exactly `committed + 1`.

**Semi-formal property:** For all time:

- `□ ( ∀ T,x : committed[T,x] ∈ Nat )`
- `□ ( ∀ T,x : pending[T,x] = None ∨ pending[T,x] = committed[T,x] + 1 )`
- Plus the implicit TLA+ frame condition that only `CommitPending` and `SyncFromPredecessor` can increase `committed[T,x]`.

## 5. Safety: Single Commit per Version per Target

**Informal:** A given version for a given chunk at a target is committed at most once; duplicate writes with the same version are idempotent.

**Semi-formal intuition:** In TLA+ we’ll enforce this structurally:

- `CommitPending(T,x)` moves `pending[T,x]` into `committed[T,x]` and sets `pending[T,x] := None`.
- No action can decrease `committed[T,x]`.

A separate invariant can assert:

- `□ ( ∀ T,x : (Changed(committed[T,x]) ⇒ committed'[T,x] = pending[T,x]) )`

where `Changed(e)` is the standard TLA+ macro indicating `e' ≠ e`.

## 6. Safety: Rebuild Correctness (Serving Implies Synced)

**Informal:** When a target transitions into `serving`, it has already synced its committed state from its predecessor; from that point on, it never falls behind.

**Semi-formal property:** For all time:

- `□ ( ∀ T,x : state[T] = serving ⇒ committed[T,x] ≥ max_{P ∈ Preds(T)} committed[P,x] )`

For the simplified model with linear chain, this reduces to predecessor relation above.

Additionally, we can express that the transition into `serving` occurs only from `syncing` and only when a `synced` flag is set:

- `□ ( state'[T] = serving ∧ state[T] ≠ serving ⇒ state[T] = syncing ∧ Synced[T] )`

## 7. Safety: Pending Version Visibility

**Informal:** Pending versions are never visible to strict reads on serving targets. Relaxed reads may see pending versions, but only for the latest write, and never a "future" version.

**Semi-formal property (strict reads):**

- `□ ( ∀ T,x,v : state[T] = serving ∧ StrictReadResult(T,x,v) ⇒ v = committed[T,x] )`

We will encode relaxed reads separately and ensure they respect `pending[T,x] ≤ committed[T,x] + 1`.

## 8. Liveness: Write Completion Under Bounded Failures

**Assumptions:**
- Head and at least one tail eventually remain `serving` (no infinite churn).
- Mgmtd eventually detects failures and stabilizes chain version.
- Network channels between serving nodes are fair (messages are eventually delivered or failure is detected).

**Informal:** Under the above assumptions, any write issued by the client is eventually either rejected definitively or completed and becomes visible to strict reads.

**Semi-formal property:** For all chunks `x`:

- `□ ( IssueWrite(x,data) ⇒ ◇ ( CompletedWrite(x,v) ∨ WriteFailed(x) ) )`

We can also add a read-after-write liveness:

- `□ ( CompletedWrite(x,v) ⇒ ◇ ( ∃ T : state[T] = serving ∧ StrictReadResult(T,x,v') ∧ v' ≥ v ) )`

## 9. Priority and Scope

We will prioritize checking the following core safety properties in the TLA+ model:

1. **S1 – No stale strict reads:** Property 1.
2. **S2 – Serving targets up-to-date w.r.t predecessor:** Property 2.
3. **S3 – Pending version invariant:** Property 4 + 7 for strict reads.
4. **S4 – Rebuild correctness:** Property 6.

Liveness properties (8) will be modeled but may be checked in weaker forms due to state-space explosion, e.g., as strong fairness on actions or via bounded liveness checks.
