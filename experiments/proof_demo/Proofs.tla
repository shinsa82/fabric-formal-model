------------------------------- MODULE Proofs -------------------------------
EXTENDS Integers

THEOREM 2 + 1 = 3
    OBVIOUS 

THEOREM Th1 == TRUE
OBVIOUS

CONSTANTS P, Q
THEOREM Th2 == P /\ Q => Q /\ P
OBVIOUS 

AXIOM Lhs == P /\ Q
THEOREM Th3 == Lhs => Q /\ P
OBVIOUS 

Rhs == P /\ Q
THEOREM Th4 == Lhs => Rhs
    BY DEF Rhs

THEOREM Th5 == \E x \in Int: x + 1 = 6
<1>1. WITNESS 5 \in Int
<1> QED BY <1>1

THEOREM Th5b == \E x \in 1..10: x + 1 = 6
OBVIOUS

THEOREM Th5c == \E x: x + 1 = 6
<1>1. WITNESS 5
<1> QED BY <1>1

CONSTANTS x
AXIOM PosX == x \in Int
THEOREM Tac_1 == x \in Int /\ x > 0 => (x + 1) * (x + 1) > 1
<1> SUFFICES
    ASSUME x \in Int, x > 0
    PROVE (x + 1) * (x + 1) > 1
    OBVIOUS
<1>1. x + 1 > 1
    OBVIOUS 
<1> QED
    BY <1>1

THEOREM Tac_Witness == \E z: z * z - 4 * z + 3 = 0
<1>1. WITNESS 1
<1> QED BY <1>1

=============================================================================
\* Modification History
\* Last modified Sun Mar 24 19:25:10 JST 2019 by shinsa
\* Created Sat Mar 23 14:25:19 JST 2019 by shinsa
