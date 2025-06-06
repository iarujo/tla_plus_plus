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

Termination == [] (\E v \in Values: EnoughVotes(v) => <>[] AllDecided(v))

-----------------------------------------------------------------------------

Init == /\ network = {} 
        /\ decided = [a \in acceptors |-> -1]


Send(m) == network' = network \cup {m}

             
Decide(a) == /\ \E v \in QuorumAgreedValues: decided' = [decided EXCEPT ![a] = v]
             /\ UNCHANGED network
             
            
CastVote(a, v) == /\ ~hasVoted(a)
                  /\ Send([type |-> "vote", acc |-> a, val |-> v])
                  /\ UNCHANGED decided
                  
CastVoteByzantine(b, v) == /\ Send([type |-> "vote", acc |-> b, val |-> v])    
                           /\ UNCHANGED decided              

Next  == \/ \E a \in Acceptor: \E v \in Values: CastVote(a, v)
         \/ \E b \in ByzantineAcceptor: \E v \in Values: CastVoteByzantine(b, v)
         \/ \E a \in acceptors: Decide(a)

Spec == Init /\ [][Next]_<<network, decided>> /\ WF_<<network, decided>>(Next)



Inv == TypeOK /\ Agreement

=============================================================================
\* Modification History
\* Last modified Wed Mar 05 11:30:27 CET 2025 by inesaraujocanas
\* Created Wed Feb 26 09:30:30 CET 2025 by inesaraujocanas