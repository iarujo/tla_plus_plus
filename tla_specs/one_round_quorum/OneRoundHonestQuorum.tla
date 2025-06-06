--------------------- MODULE SimpleOneRoundHonestQuorun ---------------------

EXTENDS Integers, FiniteSets

CONSTANTS Values, Acceptor, Quorum

ASSUME QuorumAssumption == Quorum <= Cardinality(Acceptor) /\ Quorum > 0

-----------------------------------------------------------------------------
VARIABLE votes \* votes[a] is the set of votes cast by acceptor a

TypeOK == votes \in [Acceptor -> SUBSET (Values)]
-----------------------------------------------------------------------------
\* chosen == {v \in Values : \E Q \in Quorum: \A a \in Q: v \in votes[a]}

\* chosenExists == \E Q \in Quorum: \A a1, a2 \in Q: votes[a1] = votes[a2]

hasVoted(a) == \E v \in Values: v \in votes[a]
-----------------------------------------------------------------------------
\* TODO: write invariants and properties
-----------------------------------------------------------------------------
Init == /\ votes = [a \in Acceptor |-> {}]

\* Acceptor a votes for value v, provided it hasn't already voted
castVote(a, v) == /\ ~hasVoted(a)
                  /\ votes' = [votes EXCEPT ![a] = @ \cup {v}]

\* If there is a majority, 
Next  == \E a \in Acceptor: \E v \in Values: castVote(a, v)

Spec == Init /\ [][Next]_<<votes>>

Inv == TypeOK
-----------------------------------------------------------------------------
THEOREM Invariance == Spec => []Inv
=============================================================================
\* Modification History
\* Last modified Wed Feb 26 13:54:06 CET 2025 by inesaraujocanas
\* Created Wed Feb 26 13:53:47 CET 2025 by inesaraujocanas