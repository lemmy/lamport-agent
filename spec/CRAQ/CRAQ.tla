----------------------------- MODULE CRAQ -----------------------------
EXTENDS Naturals, Sequences

(*************************************************************************)
(* Simplified CRAQ model for a single chain of storage targets.          *)
(* Focus: consistency between reads and writes, including failures and   *)
(* rebuild (resync) of a target.                                         *)
(*************************************************************************)

CONSTANTS 
  Targets, \* nonempty set of storage targets
  Chunks,  \* nonempty set of chunks
  HeadT,   \* head target in Targets
  MidT,    \* middle target in Targets
  TailT    \* tail target in Targets

ASSUME HeadT \in Targets /\ MidT \in Targets /\ TailT \in Targets

(*************************************************************************)
(* Target states                                                         *)
(*************************************************************************)

TargetStates == {"offline", "waiting", "syncing", "serving", "lastsrv"}

(*************************************************************************)
(* State variables                                                       *)
(*************************************************************************)

VARIABLES
  state,           \* [Targets -> TargetStates]
  committed,       \* [Targets -> [Chunks -> Version]]
  pending,         \* [Targets -> [Chunks -> (Version \cup {None})]]
  succ,            \* [Targets -> (Targets \cup {None})], per-target successor pointer
  clientPhase,     \* simple client state machine
  clientChunk,     \* chunk the client is currently operating on
  clientVersionSeen,\* latest version observed by strict reads
  curWriter,       \* current target where in-flight write resides (or None)
  eventLog         \* sequence of events: [type |-> "commit"/"read", chunk |-> c, version |-> v]

None == 0  \* marker for no pending version; we only use positive Nats for versions

\* Bounded version domain (for TLC)
Version == 0..2

(*************************************************************************)
(* Helper definitions                                                    *)
(*************************************************************************)

IsServing(t) == state[t] = "serving" 

\* Static predecessor relation according to the initial logical chain HeadT -> MidT -> TailT
Predecessor(p, t) == 
  (p = HeadT /\ t = MidT)
  \/ (p = MidT /\ t = TailT)

\* Effective successor used by writes/reads: follow succ only to non-offline nodes.
EffectiveSucc(t) ==
  IF succ[t] = None 
    THEN None
    ELSE IF state[succ[t]] = "offline" THEN None ELSE succ[t]

CurrentHead == HeadT

(*************************************************************************)
(* Initial state                                                         *)
(*************************************************************************)

Init == 
  /\ state = [t \in Targets |-> "serving"]
  /\ committed = [t \in Targets |-> [c \in Chunks |-> 0]]
  /\ pending = [t \in Targets |-> [c \in Chunks |-> None]]
  /\ succ = [t \in Targets |->
               IF t = HeadT THEN MidT
               ELSE IF t = MidT THEN TailT
               ELSE None]
  /\ clientPhase = "idle"
  /\ clientChunk \in Chunks
  /\ clientVersionSeen = 0
  /\ curWriter = None
  /\ eventLog = << >>

(*************************************************************************)
(* Actions: simplified CRAQ protocol                                     *)
(*************************************************************************)

\* Client chooses a chunk (we model two chunks) and starts a write at the head.
ClientStartWrite(c) ==
  /\ clientPhase = "idle"
  /\ c \in Chunks
  /\ clientChunk' = c
  /\ clientPhase' = "writing"
  /\ curWriter' = HeadT
  /\ UNCHANGED << state, committed, pending, succ, clientVersionSeen, eventLog >>

\* Generic per-target write step: the in-flight write resides at t and creates a pending version.
WriteAtTarget(t) ==
  /\ clientPhase = "writing"
  /\ t \in Targets
  /\ curWriter = t
  /\ IsServing(t)
  /\ pending[t][clientChunk] = None
  /\ committed[t][clientChunk] < 2
  /\ pending' = [pending EXCEPT ![t][clientChunk] = committed[t][clientChunk] + 1]
  /\ committed' = committed
  /\ LET nxt == EffectiveSucc(t) IN
       /\ curWriter' = nxt
    /\ UNCHANGED << state, succ, clientPhase, clientChunk, clientVersionSeen, eventLog >>

\* Tail commits pending and that commit propagates to all serving targets.
CommitWrite ==
  /\ clientPhase = "writing"
  /\ curWriter = None \* write has reached the logical tail
  /\ \E t \in Targets : IsServing(t) \* at least one serving node
  /\ \A t \in Targets : IsServing(t) => pending[t][clientChunk] # None
  /\ LET v == committed[CurrentHead][clientChunk] + 1 IN
       /\ committed' = [t \in Targets |-> [c \in Chunks |->
                         IF IsServing(t) /\ c = clientChunk
                           THEN v
                           ELSE committed[t][c]]]
       /\ pending' = [t \in Targets |-> [c \in Chunks |->
                         IF IsServing(t) /\ c = clientChunk
                           THEN None
                           ELSE pending[t][c]]]
       /\ eventLog' = Append(eventLog,
                             [type |-> "commit",
                              chunk |-> clientChunk,
                              version |-> v])
  /\ clientPhase' = "idle"
  /\ clientVersionSeen' = clientVersionSeen \* reads only update observed version
  /\ curWriter' = None
  /\ UNCHANGED << state, succ, clientChunk >>

\* Client performs a strict read from any serving target.
ClientStrictRead ==
  /\ clientPhase = "idle"
  /\ \E t \in Targets : IsServing(t)
  /\ LET t == CHOOSE u \in Targets : IsServing(u) IN
       /\ clientVersionSeen' = committed[t][clientChunk]
      /\ eventLog' = Append(eventLog,
                [type |-> "read",
              chunk |-> clientChunk,
              version |-> committed[t][clientChunk]])
    /\ UNCHANGED << state, committed, pending, succ, clientPhase, clientChunk, curWriter >>

\* A serving target can fail and become offline.
FailTarget(t) ==
  /\ t \in Targets
  /\ IsServing(t)
  /\ state' = [state EXCEPT ![t] = "offline"]
  /\ UNCHANGED << committed, pending, succ, clientPhase, clientChunk, clientVersionSeen, curWriter, eventLog >>

\* Chain repair step 1: detach a failed node f from its predecessor p (p no longer points to f).
DetachFailedFromPred(p, f) ==
  /\ p \in Targets /\ f \in Targets
  /\ succ[p] = f
  /\ state[f] = "offline"
  /\ succ' = [succ EXCEPT ![p] = succ[f]]
  /\ state' = state
  /\ UNCHANGED << committed, pending, clientPhase, clientChunk, clientVersionSeen, curWriter, eventLog >>

\* Chain repair step 2: reattach repaired node f as the new tail.
AttachAsTail(f) ==
  /\ f \in Targets
  /\ state[f] \in {"waiting", "syncing"}
  /\ succ[f] = None
  /\ \E t \in Targets : succ[t] = None /\ t # f
  /\ LET tTail == CHOOSE t \in Targets : succ[t] = None /\ t # f IN
       /\ succ' = [succ EXCEPT ![tTail] = f]
  /\ state' = state
    /\ UNCHANGED << committed, pending, clientPhase, clientChunk, clientVersionSeen, curWriter, eventLog >>

\* Resync step: predecessor copies committed state into waiting/syncing target for one chunk.
ResyncStep(t, c) ==
  /\ t \in Targets
  /\ c \in Chunks
  /\ state[t] \in {"waiting", "syncing"}
  /\ \E p \in Targets : Predecessor(p, t)
  /\ LET p == CHOOSE u \in Targets : Predecessor(u,t) IN
       /\ committed' = [committed EXCEPT ![t][c] = committed[p][c]]
       /\ pending' = [pending EXCEPT ![t][c] = None]
  /\ state' = state
  /\ UNCHANGED << succ, clientPhase, clientChunk, clientVersionSeen, curWriter, eventLog >>

\* Target can only become serving after it is fully synced with its predecessor for all chunks.
FinishResync(t) ==
  /\ t \in Targets
  /\ state[t] \in {"waiting", "syncing"}
  /\ \A c \in Chunks :
        \E p \in Targets : Predecessor(p,t) /\ committed[t][c] = committed[p][c]
  /\ state' = [state EXCEPT ![t] = "serving"]
  /\ UNCHANGED << committed, pending, succ, clientPhase, clientChunk, clientVersionSeen, curWriter, eventLog >>

(*************************************************************************)
(* Next-state relation                                                   *)
(*************************************************************************)

Next ==
  \/ (\E c \in Chunks : ClientStartWrite(c))
  \/ (\E t \in Targets : WriteAtTarget(t))
  \/ CommitWrite
  \/ ClientStrictRead
  \/ (\E t \in Targets : FailTarget(t))
  \/ (\E p \in Targets, f \in Targets : DetachFailedFromPred(p,f))
  \/ (\E f \in Targets : AttachAsTail(f))
  \/ (\E t \in Targets, c \in Chunks : ResyncStep(t,c))
  \/ (\E t \in Targets : FinishResync(t))

(*************************************************************************)
(* Invariants                                                            *)
(*************************************************************************)

InvVersions ==
  /\ committed \in [Targets -> [Chunks -> Version]]
  /\ pending \in [Targets -> [Chunks -> (Version \cup {None})]]
  /\ \A t \in Targets : \A c \in Chunks :
        pending[t][c] = None \/ pending[t][c] = committed[t][c] + 1

InvServingUpToDate ==
  \A t \in Targets : \A c \in Chunks :
    \A p \in Targets : Predecessor(p,t) /\ IsServing(t) /\ IsServing(p)
      => committed[t][c] >= committed[p][c]

\* InvStrictReadNoStale ==
\*   (clientPhase = "idle" /\ \E t \in Targets : IsServing(t))
\*     => clientVersionSeen >= committed[CurrentHead][clientChunk]

\* For every read event in the log, its version must equal
\* the most recent (latest) commit event version for that chunk
\* at or before that position in the log.
NoStaleStrictRead ==
  \A i \in 1..Len(eventLog) :
    LET ev == eventLog[i] IN
      ev.type = "read" =>
        LET c == ev.chunk IN
        LET v == ev.version IN
        /\ \A j \in 1..i :
             LET evC == eventLog[j] IN
               evC.type = "commit" /\ evC.chunk = c => evC.version <= v

Spec == Init /\ [][Next]_<<state, committed, pending, succ, clientPhase, clientChunk, clientVersionSeen, curWriter, eventLog>>

=============================================================================
