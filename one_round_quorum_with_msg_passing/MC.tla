---- MODULE MC ----
EXTENDS OneRoundHonestQuorum, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3
----

\* MV CONSTANT definitions Acceptor
const_1740571424430177000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions Values
const_1740571424430178000 == 
{v1, v2, v3}
----

\* SYMMETRY definition
symm_1740571424430179000 == 
Permutations(const_1740571424430177000) \union Permutations(const_1740571424430178000)
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_1740571424430180000 == 
{{a1, a2},{a1, a3}, {a2, a3}}
----

=============================================================================
\* Modification History
\* Created Wed Feb 26 13:03:44 CET 2025 by inesaraujocanas
