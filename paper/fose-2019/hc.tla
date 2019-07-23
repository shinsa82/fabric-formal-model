---------------------------- MODULE HourClock ------------------------------
\* Hour Clock example from Lamport's book

EXTENDS Naturals
VARIABLES hr

Init == hr \in 1..12
Next == hr' = IF hr /= 12 THEN hr+1 ELSE 1

Spec == Init /\ [][Next]_hr

THEOREM TypeSafety == Spec => []Init 
============================================================================
