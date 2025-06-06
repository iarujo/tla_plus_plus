------------------------ MODULE ByzantineQuorumNew ------------------------

EXTENDS Integers, FiniteSets

CONSTANTS Values, Acceptors, NumberByzantineAcceptors, Quorum \* ByzantineAcceptors in an integer

ASSUME QuorumAssumption == Quorum <= Cardinality(Acceptors) /\ Quorum > Cardinality(Acceptors) \div 2

(***************************************************************************)
(* Set of all possible messages                                            *)
(***************************************************************************)

Message == [type : {"vote"}, acc : Acceptors, val : Values, epoch: Nat]
           
-----------------------------------------------------------------------------

VARIABLE network, decided

TypeOK == /\ network \subseteq Message
          /\ decided \in [Acceptors -> SUBSET [value: Values \cup {-1}, epoch: Nat \cup {-1}]]
          
Epoch == 0..1

-----------------------------------------------------------------------------

(*********************************************************************************************************************)
(*                                                                                                                   *)
(*                       Explanation of the abstraction we used for modelling byzantine nodes:                       *)
(*                                                                                                                   *)
(* We consider that at most NumberByzantineAcceptors nodes from Acceptors may be byzantine. This means that in the   *)
(* same epoch we may have duplicated votes from the same acceptor, voting for different values.                      *)
(*                                                                                                                   *)
(* As there are at most NumberByzantineAcceptors doing this, NumberByzantineAcceptors acceptors may issue a vote for *)
(* every possible value in the protocol.                                                                             *)
(*                                                                                                                   *)
(* These duplicated votes are not part of the network variable. Instead, we model x byzantine votes for value v as   *)
(* changing the threshold necessary for an acceptor to decide value v from  Quorum to Quorum - x,                    *)
(* where x ∈ [0, NumberByzantineAcceptors]                                                                           *)
(*                                                                                                                   *)
(*********************************************************************************************************************)

QuorumAgreedValues(e, threshold) == {v \in Values: \E Q \in SUBSET Acceptors : 
                        /\ Cardinality(Q) >= threshold
                        /\ \A a1 \in Q: [type |-> "vote", acc |-> a1, val |-> v, epoch |-> e] \in network}
                        
-----------------------------------------------------------------------------

hasVoted(a, e) == \E v \in Values: [type |-> "vote", acc |-> a, val |-> v, epoch |-> e] \in network

voted(a, v, e) ==  [type |-> "vote", acc |-> a, val |-> v, epoch |-> e] \in network

NotDecided(a, e) == \A v \in Values, ve \in decided[a]: ve # [value |-> v, epoch |-> e] 

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties of the protocol                                              *)
(***************************************************************************)

Agreement == \A a, b \in Acceptors, va, vb \in Values, e \in Epoch: [value |-> va, epoch |-> e] \in decided[a] /\ [value |-> vb, epoch |-> e] \in decided[b] => va = vb \* Checked: (for this version too) does fail when Quorum < Cardinality(Acceptors) \div 2

EnoughVotes(v, e) == Cardinality({a \in Acceptors : [type |-> "vote", acc |-> a, val |-> v, epoch |-> e] \in network}) >= Quorum

AllDecided(v, e) == \A a \in Acceptors: [value |-> v, epoch |-> e] \in decided[a]

Termination == [] (\E v \in Values, e \in Epoch: EnoughVotes(v, e) => <>[] AllDecided(v, e))

-----------------------------------------------------------------------------

Init == /\ network = {}
        /\ decided = [a \in Acceptors |-> {[epoch |-> -1, value |-> -1]}]


Send(m) == network' = network \cup {m}

\* How do you choose the amount of byzantine messages every time an Acceptor wants to decide?
Decide(a) == /\ \E e \in Epoch, x \in 0..NumberByzantineAcceptors: 
                    \E v \in QuorumAgreedValues(e, Quorum - x): 
                        /\ NotDecided(a, e)
                        /\ decided' = [decided EXCEPT ![a] = @ \cup {[value |-> v, epoch |-> e]}]
             /\ UNCHANGED network


CastVote(a, v, e) == /\ ~hasVoted(a, e)
                     /\ Send([type |-> "vote", acc |-> a, val |-> v, epoch |-> e])
                     /\ UNCHANGED decided

Next  == \/ \E a \in Acceptors, v \in Values, e \in Epoch: CastVote(a, v, e)
         \/ \E a \in Acceptors: Decide(a)

Spec == Init /\ [][Next]_<<network, decided>> /\ WF_<<network, decided>>(Next)

Inv == TypeOK /\ Agreement     

=============================================================================