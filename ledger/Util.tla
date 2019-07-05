--------------------------------- MODULE Util ---------------------------------
VARIABLE vars
CONSTANTS Init, Next, Invariant

THEOREM InvariantMeta == 
    ASSUME
        ASSUME Init PROVE Invariant,
        ASSUME Invariant, Next PROVE Invariant',
        ASSUME Invariant, UNCHANGED vars PROVE Invariant'
    PROVE Init /\ [][Next]_vars => []Invariant
PROOF
    <1>1 Init => Invariant
        OBVIOUS
    <1>2 Invariant /\ Next => Invariant'
        OBVIOUS
    <1>3 Invariant /\ UNCHANGED vars => Invariant'
        OBVIOUS
    <1> QED BY <1>1, <1>2, <1>3
================================================================================
\* Modification History
\* Last modified Fri Jul 05 13:37:36 JST 2019 by shinsa
\* Created Fri Jul 05 13:29:27 JST 2019 by shinsa
