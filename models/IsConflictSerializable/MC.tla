---- MODULE MC ----
EXTENDS SnapshotIsolation, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
T0, T1, T2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
k1, k2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions txnIds
const_1563466721960301000 == 
{T0, T1, T2}
----

\* MV CONSTANT definitions keys
const_1563466721960302000 == 
{k1, k2}
----

\* MV CONSTANT definitions values
const_1563466721960303000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_1563466721960304000 == 
Permutations(const_1563466721960301000) \union Permutations(const_1563466721960302000) \union Permutations(const_1563466721960303000)
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1563466721960305000(x) ==
UNION {[1..n -> x] : n \in Nat}
----
\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1563466721960306000 ==
1..8
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1563466721960308000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1563466721960309000 ==
IsConflictSerializable(txnHistory)
----
====================================================================================================
\* Modification History
\* Created Thu Jul 18 12:18:41 EDT 2019 by williamschultz
