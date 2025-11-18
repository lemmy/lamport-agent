----------------------------- MODULE DieHarderInstance ---------------------------- 
(***************************************************************************)
(* Concrete instance of the DieHarder problem with 3-gallon and 5-gallon  *)
(* jugs, trying to measure 4 gallons.                                     *)
(***************************************************************************)
EXTENDS Naturals

(***************************************************************************)
(* Define concrete values for the constants                               *)
(***************************************************************************)
Jug == {"jug3", "jug5"}
Capacity == [jug3 |-> 3, jug5 |-> 5]
Goal == 4

(***************************************************************************)
(* Min operator                                                           *)
(***************************************************************************)
Min(m,n) == IF m < n THEN m ELSE n

(***************************************************************************)
(* Variable and predicates                                                *)
(***************************************************************************)
VARIABLE contents

TypeOK == contents \in [Jug -> Nat]
Init == contents = [j \in Jug |-> 0]

(***************************************************************************)
(* Actions                                                                *)
(***************************************************************************)
FillJug(j)  == contents' = [contents EXCEPT ![j] = Capacity[j]]
EmptyJug(j) == contents' = [contents EXCEPT ![j] = 0]
JugToJug(j, k) == 
  LET amountPoured == Min(contents[j], Capacity[k]-contents[k])
  IN  contents' = [contents EXCEPT ![j] = @ - amountPoured,
                                   ![k] = @ + amountPoured]

Next ==  \E j \in Jug : \/ FillJug(j)
                        \/ EmptyJug(j)
                        \/ \E k \in Jug \ {j} : JugToJug(j, k)

Spec == Init /\ [][Next]_contents

NotSolved == \A j \in Jug : contents[j] # Goal

=============================================================================
