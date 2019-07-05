------------------------------ MODULE NormalClock ------------------------------
\* Hour Clock example from Lamport's book

EXTENDS Naturals
VARIABLES hr

HCInit == hr \in 1..12
HCNext == hr' = IF hr /= 12 THEN hr+1 ELSE 1

HC == HCInit /\ [][HCNext]_hr

================================================================================
\* Modification History
\* Last modified Tue Jul 02 18:49:12 JST 2019 by shinsa
\* Created Tue Jul 02 16:35:44 JST 2019 by shinsa
