------------------------- MODULE InfiniteExecution -------------------------

(***************************************************************************)
(* This is a simple example of a protocol that can execute infinitely      *)
(***************************************************************************)

EXTENDS Integers

CONSTANTS Processes, MaxDivergence

VARIABLES counters

TypeOK == counters \in [Processes -> Nat]

----------------------------------------------------------------------------

counterValues == {counters[p]: p \in Processes}

MinCounterValue == CHOOSE c1 \in counterValues:
                    \A c2 \in counterValues:
                        c1 <= c2
                        
----------------------------------------------------------------------------
                        
RespectsDivergence(c) == (c - MinCounterValue) <= MaxDivergence

----------------------------------------------------------------------------

GarbageCollection == /\ MinCounterValue > 0
                     /\ counters' = [p \in Processes |-> counters[p] - MinCounterValue]

----------------------------------------------------------------------------

IncreaseCounter(p) == /\ ~ENABLED GarbageCollection
                      /\ RespectsDivergence(counters[p] + 1)
                      /\ counters' = [counters EXCEPT ![p] = @ + 1]
                      
----------------------------------------------------------------------------

BoundedDivergence == \A c \in counterValues: RespectsDivergence(c)

----------------------------------------------------------------------------

Monotonic == \A p \in Processes: counters'[p] >= counters[p]

Monotonicity == [][
                    \/ Monotonic
                    \/ \A p1, p2 \in Processes:
                           (counters'[p1] - counters[p1]) = (counters'[p2] - counters[p2])
                ]_counters
----------------------------------------------------------------------------

Init == counters = [p \in Processes |-> 0]

Next == \/ GarbageCollection
        \/ \E p \in Processes: IncreaseCounter(p)

Spec == Init /\ [][Next]_counters

Inv == TypeOK /\ BoundedDivergence

=============================================================================
\* Modification History
\* Last modified Thu Mar 06 16:14:17 CET 2025 by inesaraujocanas
\* Created Thu Mar 06 15:20:48 CET 2025 by inesaraujocanas
