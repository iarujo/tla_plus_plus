---------------------- MODULE OneRoundByzantineQuorum ----------------------

EXTENDS Integers, FiniteSets

CONSTANTS Values, Acceptor, ByzantineAcceptor, Quorum

acceptors == Acceptor \cup ByzantineAcceptor

ASSUME QuorumAssumption == Quorum <= Cardinality(acceptors) /\ Quorum > Cardinality(acceptors) \div 2

(***************************************************************************)
(* Set of all possible messages                                            *)
(***************************************************************************)

Message == [type : {"vote"}, acc : acceptors, val : Values]
           \* \cup Another msg type
           
-----------------------------------------------------------------------------

VARIABLE network, decided \* network is the set of all sent messages

TypeOK == /\ network \subseteq Message 
          /\ decided \in [acceptors -> Values \cup {-1}]

-----------------------------------------------------------------------------

QuorumAgreedValues == {v \in Values : \E Q \in SUBSET acceptors : 
                        /\ Cardinality(Q) >= Quorum
                        /\ \A a \in Q: [type |-> "vote", acc |-> a, val |-> v] \in network}
                        
-----------------------------------------------------------------------------

hasVoted(a) == \E v \in Values: [type |-> "vote", acc |-> a, val |-> v] \in network

voted(a, v) ==  [type |-> "vote", acc |-> a, val |-> v] \in network

-----------------------------------------------------------------------------

Agreement == \A a, b \in acceptors, va, vb \in Values: decided[a] = va /\ decided[b] = vb => va = vb \* Checked: this invariant does not hold for current model configuration (remove from Inv to simulate all states)

EnoughVotes(v) == Cardinality({a \in acceptors : [type |-> "vote", acc |-> a, val |-> v] \in network}) >= Quorum

AllDecided(v) == \A a \in acceptors: decided[a] = v

Termination == \A v \in Values: EnoughVotes(v) => <>[] AllDecided(v) \* Never violated. Is there maybe an issue here?

-----------------------------------------------------------------------------

Init == /\ network = {} 
        /\ decided = [a \in acceptors |-> -1]


Send(m) == network' = network \cup {m}

Decide(a) == \/ /\ decided[a] = -1 
                /\ \E v \in QuorumAgreedValues: decided' = [decided EXCEPT ![a] = v]
             \/ decided' = decided

\* Acceptor a votes for value v, provided it hasn't already voted
CastVote(a, v) == /\ ~hasVoted(a)
                  /\ Send([type |-> "vote", acc |-> a, val |-> v])
                  
\* A Byzantine node can send any type of message whenever it wants. 
\* It can also vote for as many values as it wants. Voting for different values at the same time essentially means
\* that Acceptors can store different values for b's vote
CastVoteByzantine(b, v) == Send([type |-> "vote", acc |-> b, val |-> v])                  

Next  == /\(\/ \E a \in Acceptor: \E v \in Values: CastVote(a, v)
            \/ \E b \in ByzantineAcceptor: \E v \in Values: CastVoteByzantine(b, v))
         /\ \E a \in acceptors: Decide(a)

Spec == Init /\ [][Next]_<<network, decided>> /\ Termination

Inv == TypeOK /\ Agreement

=============================================================================
