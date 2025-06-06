------------------------ MODULE OneRoundHonestQuorum ------------------------

EXTENDS Integers, FiniteSets

CONSTANTS Values, Acceptor, Quorum

ASSUME QuorumAssumption == Quorum <= Cardinality(Acceptor) /\ Quorum > Cardinality(Acceptor) \div 2

(***************************************************************************)
(* Set of all possible messages                                            *)
(***************************************************************************)
Message == [type : {"vote"}, acc : Acceptor, val : Values]
           \* \cup Another msg type
           
-----------------------------------------------------------------------------

VARIABLE network, decided \* network is the set of all sent messages

TypeOK == /\ network \subseteq Message 
          /\ decided \in [Acceptor -> Values \cup {-1}]

-----------------------------------------------------------------------------

QuorumAgreedValues == {v \in Values : \E Q \in SUBSET Acceptor : 
                        /\ Cardinality(Q) >= Quorum
                        /\ \A a1 \in Q: [type |-> "vote", acc |-> a1, val |-> v] \in network}
                        
-----------------------------------------------------------------------------

hasVoted(a) == \E v \in Values: [type |-> "vote", acc |-> a, val |-> v] \in network

voted(a, v) ==  [type |-> "vote", acc |-> a, val |-> v] \in network

-----------------------------------------------------------------------------

Agreement == \A a, b \in Acceptor, va, vb \in Values: decided[a] = va /\ decided[b] = vb => va = vb \* Checked: does fail when Quorum < Cardinality(Acceptor) \div 2

EnoughVotes(v) == Cardinality({a \in Acceptor : [type |-> "vote", acc |-> a, val |-> v] \in network}) >= Quorum

AllDecided(v) == \A a \in Acceptor: decided[a] = v

Termination == [] (\E v \in Values: EnoughVotes(v) => <>[] AllDecided(v))

\* Ev == [] (\A v \in Values: EnoughVotes(v) = FALSE)

-----------------------------------------------------------------------------

Init == /\ network = {} 
        /\ decided = [a \in Acceptor |-> -1]


Send(m) == network' = network \cup {m}

Decide(a) == /\ \E v \in QuorumAgreedValues: decided' = [decided EXCEPT ![a] = v]
             /\ UNCHANGED network
      

CastVote(a, v) == /\ ~hasVoted(a)
                  /\ Send([type |-> "vote", acc |-> a, val |-> v])
                  /\ UNCHANGED decided

\* For now, stop once everyone has cast a vote
Next  == \/ \E a \in Acceptor: \E v \in Values: CastVote(a, v)
         \/ \E a \in Acceptor: Decide(a)

Spec == Init /\ [][Next]_<<network, decided>> /\ WF_<<network, decided>>(Next)

Inv == TypeOK /\ Agreement

=============================================================================
\* Modification History
\* Last modified Wed Mar 05 11:21:31 CET 2025 by inesaraujocanas
\* Created Wed Feb 26 09:30:30 CET 2025 by inesaraujocanas