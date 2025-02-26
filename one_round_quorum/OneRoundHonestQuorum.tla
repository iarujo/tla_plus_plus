------------------------ MODULE OneRoundHonestQuorum ------------------------
CONSTANTS Values, Acceptor, Quorum
-----------------------------------------------------------------------------
ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
-----------------------------------------------------------------------------
VARIABLE votes \* votes[a] is the set of votes cast by acceptor a

TypeOK == votes \in [Acceptor -> SUBSET (Values)]
-----------------------------------------------------------------------------
chosen == {v \in Values : \E Q \in Quorum: \A a \in Q: v \in votes[a]}

chosenExists == \E Q \in Quorum: \A a1, a2 \in Q: votes[a1] = votes[a2]

hasVoted(a) == \E v \in Values: v \in votes[a]

allHaveVoted == \A a \in Acceptor: hasVoted(a)
-----------------------------------------------------------------------------
\* TODO: write invariants and properties
-----------------------------------------------------------------------------
Init == /\ votes = [a \in Acceptor |-> {}]

\* Acceptor a votes for value v, provided it hasn't already voted
castVote(a, v) == /\ ~hasVoted(a)
                  /\ votes' = [votes EXCEPT ![a] = @ \cup {v}]

\* For now, we stop once everyone has voted
Next  == /\ ~allHaveVoted
         /\ \E a \in Acceptor: \E v \in Values: castVote(a, v)

Spec == Init /\ [][Next]_<<votes>>

Inv == TypeOK
-----------------------------------------------------------------------------
THEOREM Invariance == Spec => []Inv
=============================================================================
\* Modification History
\* Last modified Wed Feb 26 10:43:31 CET 2025 by inesaraujocanas
\* Created Wed Feb 26 09:30:30 CET 2025 by inesaraujocanas
