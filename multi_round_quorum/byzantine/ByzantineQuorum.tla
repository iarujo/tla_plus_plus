-------------------------- MODULE ByzantineQuorum --------------------------

EXTENDS Integers, FiniteSets

CONSTANTS Values, Acceptor, ByzantineAcceptor, Quorum

acceptors == Acceptor \cup ByzantineAcceptor

ASSUME QuorumAssumption == Quorum <= Cardinality(acceptors) /\ Quorum > Cardinality(acceptors) \div 2

(***************************************************************************)
(* Set of all possible messages                                            *)
(***************************************************************************)
Message == [type : {"vote"}, acc : acceptors, val : Values, epoch: Nat]
           \* \cup Another msg type
           
-----------------------------------------------------------------------------

VARIABLE network, decided \* network is the set of all sent messages

TypeOK == /\ network \subseteq Message 
          /\ decided \in [acceptors -> SUBSET [value: Values \cup {-1}, epoch: Nat \cup {-1}]]
          
Epoch == 0..1

-----------------------------------------------------------------------------

QuorumAgreedValues(e) == {v \in Values: \E Q \in SUBSET acceptors : 
                        /\ Cardinality(Q) >= Quorum
                        /\ \A a1 \in Q: [type |-> "vote", acc |-> a1, val |-> v, epoch |-> e] \in network}
                        
-----------------------------------------------------------------------------

hasVoted(a, e) == \E v \in Values: [type |-> "vote", acc |-> a, val |-> v, epoch |-> e] \in network

voted(a, v, e) ==  [type |-> "vote", acc |-> a, val |-> v, epoch |-> e] \in network

-----------------------------------------------------------------------------

Agreement == \A a, b \in acceptors, va, vb \in Values, e \in Epoch: [value |-> va, epoch |-> e] \in decided[a] /\ [value |-> vb, epoch |-> e] \in decided[b] => va = vb \* Checked: (for this version too) does fail when Quorum < Cardinality(Acceptor) \div 2

EnoughVotes(v, e) == Cardinality({a \in acceptors : [type |-> "vote", acc |-> a, val |-> v, epoch |-> e] \in network}) >= Quorum

AllDecided(v, e) == \A a \in acceptors: [value |-> v, epoch |-> e] \in decided[a]

Termination == \A v \in Values, e \in Epoch: EnoughVotes(v, e) => <>[] AllDecided(v, e)

-----------------------------------------------------------------------------

Init == /\ network = {}
        /\ decided = [a \in acceptors |-> {[epoch |-> -1, value |-> -1]}]


Send(m) == network' = network \cup {m}

\* Decide only if you haven't previously decided a value for epoch e
Decide(a) == \/ \E e \in Epoch: \E v \in QuorumAgreedValues(e): 
                    \A ve \in decided[a]: 
                        /\ ve # [value |-> v, epoch |-> e] 
                        /\ decided' = [decided EXCEPT ![a] = @ \cup {[value |-> v, epoch |-> e]}]
             \/ decided' = decided

CastVote(a, v, e) == /\ ~hasVoted(a, e)
                     /\ Send([type |-> "vote", acc |-> a, val |-> v, epoch |-> e])
            
\* A Byzantine node can send any type of message whenever it wants. 
\* It can also vote for as many values as it wants. Voting for different values at the same epoch essentially means
\* that Acceptors can store different values for b's vote      
CastVoteByzantine(a, v, e) == Send([type |-> "vote", acc |-> a, val |-> v, epoch |-> e])

Next  == /\(\/ \E a \in Acceptor, v \in Values, e \in Epoch: CastVote(a, v, e)
            \/ \E a \in ByzantineAcceptor, v \in Values, e \in Epoch: CastVoteByzantine(a, v, e))
         /\ \E a \in Acceptor: Decide(a)

Spec == Init /\ [][Next]_<<network, decided>> /\ Termination

Inv == TypeOK \*/\ Agreement


=============================================================================
