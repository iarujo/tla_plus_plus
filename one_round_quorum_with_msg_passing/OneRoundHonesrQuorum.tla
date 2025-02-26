------------------------ MODULE OneRoundHonestQuorum ------------------------
CONSTANTS Values, Acceptor, Quorum
-----------------------------------------------------------------------------
ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}

(***************************************************************************)
(* Set of all possible messages                                            *)
(***************************************************************************)
Message == [type : {"vote"}, acc : Acceptor, val : Values]
           \* \cup Another msg type
           
-----------------------------------------------------------------------------

VARIABLE votes, network \* votes[a] is the set of votes acceptor a has observed, network is the set of all sent messages

TypeOK == /\ votes \in [Acceptor -> [Acceptor -> SUBSET (Values)]] 
          /\ network \subseteq Message

-----------------------------------------------------------------------------

decided(a) == {v \in Values : \E Q \in Quorum: \A acc \in Q: v \in votes[a][acc]}

\* Check if Acceptor a has already received a vote from Acceptor b
hasVoted(a, b) == \E v \in Values: v \in votes[a][b]

\* All acceptors have already cast a vote into the network
allHaveVoted == \A a \in Acceptor: hasVoted(a, a)

-----------------------------------------------------------------------------
\* TODO: write invariants and properties
-----------------------------------------------------------------------------

Init == /\ votes = [a1 \in Acceptor |-> [a2 \in Acceptor |-> {}]] 
        /\ network = {}


Send(m) == network' = network \cup {m}

Receive(a) == \E m \in network : 
                /\ m.type = "vote"
                /\ m.acc # a  \* Ignore messages from the acceptor itself
                /\ ~hasVoted(a, m.acc)  \* Ensure acceptor a has not already voted
                /\ votes' = [votes EXCEPT ![a] = [@ EXCEPT ![m.acc] = @ \cup {m.val}]]
                /\ network' = network


\* Acceptor a votes for value v, provided it hasn't already voted
castVote(a, v) == /\ ~hasVoted(a, a)
                  /\ votes' = [votes EXCEPT ![a] = [@ EXCEPT ![a] = @ \cup {v}]] \* Is this correct?
                  /\ Send([type |-> "vote", acc |-> a, val |-> v])

\* For now, stop once everyone has cast a vote
Next  == \/ /\ ~allHaveVoted
            /\ \E a \in Acceptor: \E v \in Values: castVote(a, v)
         \/ \E a \in Acceptor: Receive(a)

Spec == Init /\ [][Next]_<<votes, network>>

Inv == TypeOK

=============================================================================
\* Modification History
\* Last modified Wed Feb 26 13:03:27 CET 2025 by inesaraujocanas
\* Created Wed Feb 26 09:30:30 CET 2025 by inesaraujocanas