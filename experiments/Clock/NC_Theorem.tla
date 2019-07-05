------------------------------ MODULE NC_Theorem ------------------------------
EXTENDS NormalClock, TLAPS

Liveness == <>(hr = 8) 
Safety == (hr \in 1..12) 

THEOREM HC => Liveness
    OMITTED

(* Lemma for progress of safety *)
LEMMA Progress == Safety /\ HCNext => Safety'
<2> USE DEF Safety
<2>1. hr /= 12 \/ hr = 12
    OBVIOUS
<2>2. CASE hr /= 12
    BY DEF HCNext
<2>3. CASE hr = 12
    BY DEF HCNext
<2>4. QED
    BY <2>1, <2>2, <2>3

THEOREM HC => []Safety
<1> USE DEF Safety
<1>1. HCInit => Safety \* We want to refer to non-temporal part of Safety!
    BY DEF HCInit 
<1>2. Safety /\ HCNext => Safety'
    BY Progress
<1>3. Safety /\ UNCHANGED hr => Safety'
    OBVIOUS
<1>4. QED
    BY PTL, <1>1, <1>2, <1>3 DEF HC

----
(* When safety is already in temporal form *) 

SafetyFull == [](hr \in 1..12) 

THEOREM HC => SafetyFull
<1>1. HCInit => SafetyFull!1 \* We want to refer to non-temporal part of Safety!
    BY DEF HCInit
<1>2. SafetyFull!1 /\ HCNext => SafetyFull!1'
    <2>1. hr /= 12 \/ hr = 12
        OBVIOUS
    <2>2. CASE hr /= 12
        BY DEF HCNext
    <2>3. CASE hr = 12
        BY DEF HCNext
    <2>4. QED
        BY <2>1, <2>2, <2>3
<1>3. SafetyFull!1 /\ UNCHANGED hr => SafetyFull!1'
    OBVIOUS
<1>4. HC => []SafetyFull!1
    BY PTL, <1>1, <1>2, <1>3 DEF HC
<1>5. QED
    BY <1>4 DEF SafetyFull

----
(* Can it be simpler? *)

THEOREM HC => SafetyFull
<1>1. HCInit => SafetyFull!1 \* We want to refer to non-temporal part of Safety!
    BY DEF HCInit
<1>2. SafetyFull!1 /\ HCNext => SafetyFull!1'
    OMITTED
<1>3. SafetyFull!1 /\ UNCHANGED hr => SafetyFull!1'
    OBVIOUS
<1>4. QED
    BY <1>1, <1>2, <1>3 DEF HC, SafetyFull

================================================================================
\* Modification History
\* Last modified Wed Jul 03 14:09:58 JST 2019 by shinsa
\* Created Tue Jul 02 18:00:24 JST 2019 by shinsa
