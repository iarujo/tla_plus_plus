---- MODULE MC ----
EXTENDS OneRoundByzantineQuorum, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3
----

\* MV CONSTANT definitions Acceptor
const_1740575570988275000 == 
{a1, a2}
----

\* MV CONSTANT definitions ByzantineAcceptor
const_1740575570988276000 == 
{a3}
----

\* MV CONSTANT definitions Values
const_1740575570988277000 == 
{v1, v2, v3}
----

\* SYMMETRY definition
symm_1740575570988278000 == 
Permutations(const_1740575570988275000) \union Permutations(const_1740575570988276000) \union Permutations(const_1740575570988277000)
----

\* CONSTANT definitions @modelParameterConstants:2Quorum
const_1740575570988279000 == 
2
----

=============================================================================
\* Modification History
\* Created Wed Feb 26 14:12:50 CET 2025 by inesaraujocanas
