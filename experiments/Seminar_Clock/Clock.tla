--------------------------------- MODULE Clock ---------------------------------
\* Hour Clock example from Lamport's book

EXTENDS Naturals, TLAPS

VARIABLES hr

HCInit == hr \in 1..12
HCNext == hr' = IF hr /= 12 THEN hr+1 ELSE 1

(******************************************************************************)
(* Specification.                                                             *)
(******************************************************************************)
Spec == HCInit /\ [][HCNext]_hr

\* Spec for verify liveness
FSpec == HCInit /\ [][HCNext]_hr /\ WF_hr(HCNext)

Liveness == <>(hr = 8) 
Safety == (hr \in 1..12) 

BadSafety == (hr \in 1..11)
BadLiveness == <>(hr = 13) 

----
(******************************************************************************)
(* Thorem proving examples                                                    *)
(******************************************************************************)

\* Lemma for progress of safety
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

THEOREM Spec => []Safety
<1> USE DEF Safety
<1>1. HCInit => Safety \* We want to refer to non-temporal part of Safety!
    BY DEF HCInit 
<1>2. Safety /\ HCNext => Safety'
    BY Progress
<1>3. Safety /\ UNCHANGED hr => Safety'
    OBVIOUS
<1>4. QED
    BY PTL, <1>1, <1>2, <1>3 DEF Spec

----
(* When safety is already in temporal form *) 

SafetyFull == [](hr \in 1..12) 

THEOREM Spec => SafetyFull
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
<1>4. Spec => []SafetyFull!1
    BY PTL, <1>1, <1>2, <1>3 DEF Spec
<1>5. QED
    BY <1>4 DEF SafetyFull

================================================================================
\* Modification History
\* Last modified Wed Jul 03 14:25:36 JST 2019 by shinsa
\* Created Wed Jul 03 14:11:59 JST 2019 by shinsa
