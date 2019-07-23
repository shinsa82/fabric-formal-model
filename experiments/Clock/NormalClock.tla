------------------------------ MODULE NormalClock ------------------------------
\* Hour Clock example from Lamport's book

EXTENDS Naturals
VARIABLES hr

Init == hr \in 1..12
Next == hr' = IF hr /= 12 THEN hr+1 ELSE 1

Spec == Init /\ [][Next]_hr

THEOREM TypeSafety == Spec => []Init 
================================================================================
\* Modification History
\* Last modified Mon Jul 22 13:54:24 JST 2019 by shinsa
\* Created Tue Jul 02 16:35:44 JST 2019 by shinsa
