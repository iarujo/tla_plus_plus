---- MODULE MC ----
EXTENDS SimpleOneRoundHonestQuorun, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Acceptor
const_1740574490575247000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions Values
const_1740574490575248000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_1740574490575249000 == 
Permutations(const_1740574490575247000) \union Permutations(const_1740574490575248000)
----

\* CONSTANT definitions @modelParameterConstants:1Quorum
const_1740574490575250000 == 
2
----

=============================================================================
\* Modification History
\* Created Wed Feb 26 13:54:50 CET 2025 by inesaraujocanas
