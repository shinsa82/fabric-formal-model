------------------------------ MODULE NC_Liveness ------------------------------
EXTENDS NormalClock, TLAPS

Liveness == <>(hr = 8) 
Safety == (hr \in 1..12) 

THEOREM HC => <>Liveness!1
<1> USE DEF HC
<1>1. (HCInit /\ Liveness!1) \/ (HCNext /\ Liveness)
    OMITTED
<1>10. QED
    BY PTL, <1>1

LEMMA \A: Liveness!1' => Livess 
================================================================================
\* Modification History
\* Last modified Wed Jul 03 11:06:31 JST 2019 by shinsa
\* Created Tue Jul 02 19:45:12 JST 2019 by shinsa
