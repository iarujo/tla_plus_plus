---------------------- MODULE OneRoundByzantineQuorum ----------------------

EXTENDS Integers, FiniteSets

CONSTANTS Values, Acceptor, ByzantineAcceptor, Quorum

acceptors == Acceptor \cup ByzantineAcceptor

ASSUME QuorumAssumption == Quorum <= Cardinality(Acceptor) /\ Quorum > 0

(***************************************************************************)
(* Set of all possible messages                                            *)
(***************************************************************************)

Message == [type : {"vote"}, acc : acceptors, val : Values]
           \* \cup Another msg type
           
-----------------------------------------------------------------------------

VARIABLE votes, network \* votes[a] is the set of votes acceptor a has observed, network is the set of all sent messages

TypeOK == /\ votes \in [acceptors -> [acceptors -> SUBSET (Values)]] 
          /\ network \subseteq Message

-----------------------------------------------------------------------------

decided(a) == {v \in Values : \E Q \in SUBSET Acceptor : 
               /\ Cardinality(Q) >= Quorum
               /\ \A acc \in Q: v \in votes[a][acc]}
               
\* Check if acceptors a has already received a vote from acceptors b
hasVoted(a, b) == \E v \in Values: v \in votes[a][b]

-----------------------------------------------------------------------------
\* TODO: write invariants and properties
-----------------------------------------------------------------------------

Init == /\ votes = [a1 \in acceptors |-> [a2 \in acceptors |-> {}]] 
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
                  
\* A Byzantine node can send any type of message whenever it wants. 
\* It can also vote for as many values as it wants. Voting for different values at the same time essentially means
\* that Acceptors can store different values for b's vote
castVoteByzantine(b, v) == /\ votes' = [votes EXCEPT ![b] = [@ EXCEPT ![b] = @ \cup {v}]]
                           /\ Send([type |-> "vote", acc |-> b, val |-> v])                  

\* For now, stop once everyone has cast a vote
Next  == \/ \E a \in Acceptor: \E v \in Values: castVote(a, v)
         \/ \E b \in ByzantineAcceptor: \E v \in Values: castVoteByzantine(b, v)
         \/ \E acc \in acceptors: Receive(acc)

Spec == Init /\ [][Next]_<<votes, network>>

Inv == TypeOK

=============================================================================
\* Modification History
\* Last modified Wed Feb 26 14:13:15 CET 2025 by inesaraujocanas
\* Created Wed Feb 26 13:15:23 CET 2025 by inesaraujocanas