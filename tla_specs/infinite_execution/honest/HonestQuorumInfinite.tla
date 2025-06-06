------------------------ MODULE HonestQuorumInfinite ------------------------

EXTENDS Integers, FiniteSets

CONSTANTS Values, Acceptor, Quorum, MaxDivergence

ASSUME QuorumAssumption == Quorum <= Cardinality(Acceptor) /\ Quorum > Cardinality(Acceptor) \div 2

VARIABLES network, decided, counters


(***************************************************************************)
(* Set of messages we can send to the network                              *)
(***************************************************************************)

Message == [type : {"vote"}, acc : Acceptor, val : Values, epoch: Nat]

TypeOK == /\ network \subseteq Message 
          /\ counters \in [Acceptor -> Nat]
          /\ \A a \in Acceptor: decided[a] \in SUBSET [value: Values \cup {-1}, epoch: Nat \cup {-1}]

----------------------------------------------------------------------------
(***************************************************************************)
(* Set of all values who have received votes from a quorum of acceptors    *)
(***************************************************************************)

QuorumAgreedValues(e) == {v \in Values: \E Q \in SUBSET Acceptor : 
                        /\ Cardinality(Q) >= Quorum
                        /\ \A a1 \in Q: [type |-> "vote", acc |-> a1, val |-> v, epoch |-> e] \in network}
                        
----------------------------------------------------------------------------
(***************************************************************************)
(* Garbage Collection                                                      *)
(***************************************************************************)

counterValues == {counters[p]: p \in Acceptor}

MinCounterValue == CHOOSE c1 \in counterValues:
                    \A c2 \in counterValues:
                        c1 <= c2
                                                
RespectsDivergence(c) == (c - MinCounterValue) <= MaxDivergence

GCDecided(vals) ==  {v1 \in 
                        {[epoch |-> v2.epoch - MinCounterValue, value |-> v2.value]
                            : v2 \in vals}
                                : v1.epoch >= 0}
                    \cup {[epoch |-> -1, value |-> -1]}


GarbageCollection == /\ MinCounterValue > 0
                     /\ counters' = [p \in Acceptor |-> counters[p] - MinCounterValue]
                     /\ network' = 
                        {m1 \in 
                            {[type |-> "vote", acc |-> m2.acc, val |-> m2.val, epoch |-> m2.epoch - MinCounterValue]
                             : m2 \in network}
                                : m1.epoch >= 0}
                     /\ decided' = [a \in DOMAIN decided |-> GCDecided(decided[a])]
                     
----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants and Properties about Monotonicity                            *)
(***************************************************************************)

BoundedDivergence == \A c \in counterValues: RespectsDivergence(c)

Monotonic == \A p \in Acceptor: counters'[p] >= counters[p]

Monotonicity == [][
                    \/ Monotonic
                    \/ \A a1, a2 \in Acceptor:
                           (counters'[a1] - counters[a1]) = (counters'[a2] - counters[a2])
                ]_counters
----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants and Properties from the Quorum Protocol                      *)
(***************************************************************************)

Agreement == \A a, b \in Acceptor, va, vb \in Values: \E e \in 0..counters[a]: [value |-> va, epoch |-> e] \in decided[a] /\ [value |-> vb, epoch |-> e] \in decided[b] => va = vb \* Checked: (for this version too) does fail when Quorum < Cardinality(Acceptor) \div 2

EnoughVotes(v, e) == Cardinality({a \in Acceptor : [type |-> "vote", acc |-> a, val |-> v, epoch |-> e] \in network}) >= Quorum

AllDecided(v, e) == \A a \in Acceptor: [value |-> v, epoch |-> e] \in decided[a]

\* Old definition (doesn't work for this implementation): Termination == [] (\E v \in Values: \E e \in 0..MaxDivergence: EnoughVotes(v, e) => <>[] AllDecided(v, e))

Termination == [] (\E v \in Values: \E e \in 0..MaxDivergence: EnoughVotes(v, e) => <> AllDecided(v, e))

-----------------------------------------------------------------------------

hasVoted(a, e) == \E v \in Values: [type |-> "vote", acc |-> a, val |-> v, epoch |-> e] \in network

Send(m) == network' = network \cup {m}
-----------------------------------------------------------------------------

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

                                                   \* TODO: def here's a bit weird. Can I simplify this?
Decide(a, e) == /\ \E v \in QuorumAgreedValues(e): /\ \A ve \in decided[a]: ve # [value |-> v, epoch |-> e] 
                                                   /\ decided' = [decided EXCEPT ![a] = @ \cup {[value |-> v, epoch |-> e]}]
                /\ UNCHANGED counters
                /\ UNCHANGED network
                                                                                                \* Preconditions:
CastVote(a, v) == /\ ~ENABLED GarbageCollection                                                 \* - GC is disabled
                  /\ ~hasVoted(a, counters[a])                                                  \* - Can't vote twice for the same epoch
                  /\ Send([type |-> "vote", acc |-> a, val |-> v, epoch |-> counters[a]])
                  /\ UNCHANGED decided
                  /\ UNCHANGED counters
                  
IncreaseEpoch(a) == /\ ~ENABLED GarbageCollection                                               \* Preconditions:
                    /\ \E v \in Values: [epoch |-> counters[a], value |-> v] \in decided[a]     \* - Acceptor has already decided a value for the current epoch
                    /\ \E v \in Values: hasVoted(a, counters[a])                                \* - Acceptor has already voted a value for the current epoch
                    /\ RespectsDivergence(counters[a] + 1)                                      \* - Respect divergence
                    /\ counters' = [counters EXCEPT ![a] = @ + 1]
                    /\ UNCHANGED network
                    /\ UNCHANGED decided
                      
----------------------------------------------------------------------------

Init == /\ network = {}
        /\ counters = [a \in Acceptor |-> 0]
        /\ decided = [a \in Acceptor |-> {[epoch |-> -1, value |-> -1]}]

\* TODO: Try creating Epoch = Nat and instead of passing e, to \E e \in Epoch
Next == \/ GarbageCollection
        \/ \E a \in Acceptor, v \in Values: CastVote(a, v)
        \/ \E a \in Acceptor: Decide(a, counters[a])
        \/ \E a \in Acceptor: IncreaseEpoch(a)

Spec == Init /\ [][Next]_<<network, counters, decided>> /\ WF_<<network, counters, decided>>(Next)

Inv == TypeOK /\ BoundedDivergence /\ Agreement

=============================================================================