------------------------------ MODULE Experiments ------------------------------
EXTENDS Sequences, Naturals, TLAPS

\* list == <<1,2,3>>

(******************************************************************************)
(* Sequence index starts from 1                                               *)
(******************************************************************************)
LEMMA LET list == <<1,2,3>> IN list[1] = 1
    OBVIOUS

LEMMA 3..2 = {}
    OBVIOUS
    
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
(* A proof that involves inequality *)

ChainEntry == [is_valid: BOOLEAN]
Chain == Seq(ChainEntry)

LEMMA \A s \in Chain, idx \in Nat: 0 < idx /\ idx <= Len(s) => idx \in DOMAIN s
    BY DEF Chain
     
LEMMA \A ch, ch2 \in Chain: Len(ch) > 0 /\ ch2 = [ch EXCEPT ![1].is_valid = TRUE] => ch2[1].is_valid = TRUE
    <1>1 TAKE ch, ch2 \in Chain 
    <1> SUFFICES ASSUME Len(ch) > 0, ch2 = [ch EXCEPT ![1].is_valid = TRUE] PROVE ch2[1].is_valid = TRUE BY <1>1
    <1> QED BY 1 \in DOMAIN ch DEF Chain, ChainEntry

LEMMA \A ch, ch2 \in Chain, i \in Nat: i > 0 /\ i <= Len(ch) /\ ch2 = [ch EXCEPT ![i].is_valid = TRUE] => ch2[i].is_valid = TRUE
    <1>1 TAKE ch, ch2 \in Chain, i \in Nat 
    <1> SUFFICES ASSUME i > 0, i <= Len(ch), ch2 = [ch EXCEPT ![i].is_valid = TRUE] PROVE ch2[i].is_valid = TRUE BY <1>1
    <1> QED BY i \in DOMAIN ch DEF Chain, ChainEntry

LEMMA \A ch, ch2 \in Chain, i \in Nat: i > 0 /\ i <= Len(ch) /\ ch2 = [ch EXCEPT ![i]["is_valid"] = TRUE] => ch2[i]["is_valid"] = TRUE
    <1>1 TAKE ch, ch2 \in Chain, i \in Nat 
    <1> SUFFICES ASSUME i > 0, i <= Len(ch), ch2 = [ch EXCEPT ![i].is_valid = TRUE] PROVE ch2[i].is_valid = TRUE BY <1>1
    <1> QED BY i \in DOMAIN ch DEF Chain, ChainEntry

----

(*
\* Label in a datatype
RecordList == Seq(record::Nat) 

\* Caution, this make TLAPS crash
LEMMA <<3>> \in RecordList
    OBVIOUS
*)
    
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

----
(* An inner module: all line including blank lines should be correctly indented *)

    ----- MODULE Inner -----
    EXTENDS Naturals
    
    VARIABLE innerVar
    THEOREM InnerTh == innerVar \in Nat => innerVar > 0
        OMITTED
    ========

----
(******************************************************************************)
(* Meta theorem for proving an invariant (failed)                             *)
(******************************************************************************)

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
\* Last modified Mon Jul 08 18:49:53 JST 2019 by shinsa
\* Created Thu Jul 04 16:52:28 JST 2019 by shinsa
