------------------------------- MODULE Clock -------------------------------
\* Hour Clock example from Lamport's book

EXTENDS Naturals, TLAPS
VARIABLES hr

HCInit == hr \in (1..10000000)
HCNext == hr' = IF hr /= 10000000 THEN hr+1 ELSE 1

HC == HCInit /\ [][HCNext]_hr

THEOREM HC => []HCInit 
<1> USE DEF HC
<1>1. HCInit => HCInit
  OBVIOUS
<1>2. HCInit /\ HCNext => HCInit'
  BY DEF HCInit
<1>3. HCInit /\ UNCHANGED hr => HCInit'
  BY DEF HCInit
<1> QED
  BY PTL, <1>1, <1>2, <1>3
  
NC == INSTANCE NormalClock
  
=============================================================================
\* Modification History
\* Last modified Tue Jul 02 17:03:22 JST 2019 by shinsa
\* Created Mon Apr 01 01:13:30 JST 2019 by shinsa
