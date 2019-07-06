------------------------------ MODULE Experiments ------------------------------
EXTENDS Sequences, Naturals, TLAPS

list == <<1,2,3>>

(******************************************************************************)
(* Sequence index starts from 1                                               *)
(******************************************************************************)
THEOREM list[1] = 1
    BY DEF list

CONSTANT State
Operation == [State -> (SUBSET State) \ {{}}]
TX == [f: Operation]
    
\* Universal quant. 1    
LEMMA \A tx \in TX: tx.f \in Operation
    BY DEF TX

\* Universal quant. 2    
LEMMA \A f \in Operation, s \in State: f[s] /= {}
    BY DEF Operation

\* Top level LET
LEMMA LET a == 3 IN a + 1 = 4 /\ a - 1 = 2
    OBVIOUS    

\* Inner level LET
LEMMA
    /\ 3 + 1 = 4
    /\ (LET
            a == 3
        IN
            a - 1 = 2)
    OBVIOUS    

----
\* Label in a datatype
RecordList == Seq(record::Nat) 

\* Caution, this make TLAPS crash
LEMMA <<3>> \in RecordList
    OBVIOUS
    
----
(******************************************************************************)
(* The proof by contradiction and the excluded middle                         *)
(******************************************************************************)
THEOREM ASSUME NEW P
        PROVE ~(P /\ ~P)
    OBVIOUS

THEOREM ASSUME NEW P
        PROVE P \/ ~P
    OBVIOUS

    ----- MODULE Inner -----
    EXTENDS Naturals
    
    VARIABLE innerVar
    THEOREM InnerTh == innerVar \in Nat => innerVar > 0
        OMITTED
    ========

(******************************************************************************)
(* Meta theorem for proving an invariant                                      *)
(******************************************************************************)
----
THEOREM InvMeta == 
    ASSUME
        NEW Init, ACTION Next, NEW vars, NEW Invariant,
        Init => Invariant,
        Invariant /\ Next => Invariant',
        Invariant /\ UNCHANGED vars => Invariant'
    PROVE Init /\ [][Next]_vars => []Invariant
PROOF
    OBVIOUS

THEOREM InvMeta2 == 
    ASSUME
        NEW Init, ACTION Next, VARIABLE vars, NEW Invariant,
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

\* test

VARIABLE v

II(_v) == INSTANCE Inner WITH innerVar <- _v 
OuterTh == II(v)!InnerTh

Init == v = 2
Next == v' = v + 2 
Spec == Init /\ [][Next]_v 
Inv == v > 0

THEOREM Spec => []Inv
PROOF
    <1>1 ASSUME Init PROVE Inv
        OMITTED
    <1>2 ASSUME Inv, Next PROVE Inv'
        OMITTED
    <1>3 ASSUME Inv, UNCHANGED v PROVE Inv'
        OMITTED
    <1> QED BY InvMeta2, <1>1, <1>2, <1>3 DEF Spec
================================================================================
\* Modification History
\* Last modified Sat Jul 06 00:17:49 JST 2019 by shinsa
\* Created Thu Jul 04 16:52:28 JST 2019 by shinsa
