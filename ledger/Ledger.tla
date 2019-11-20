-------------------------------- MODULE Ledger --------------------------------
(******************************************************************************)
(* High level specification of DLT Ledger,                                    *)
(* expressed as a single state machine without MVCC validation                *)
(******************************************************************************)
EXTENDS Sequences, Integers, TLAPS, Datatype

(******************************************************************************)
(* State variables of this module                                             *)
(******************************************************************************)
VARIABLES state,    \* current state of the ledger state machine.
          chain,    \* blockchain, a list of received transactions. 
          index     \* unprocessed TX index at the blockchain.
vars == <<state, chain, index>>


(******************************************************************************)
(* Datatype Definition                                                        *)
(******************************************************************************)
\* Each entry in its blockchain (chain) has a flag if it's valid or not.
\* Before the TX is processed, its value is NULL.
ChainEntry == [tx: TX, is_valid: BOOLEAN \union {NULL}] 
Chain      == Seq(ChainEntry)

----
(******************************************************************************)
(* Initial condition                                                          *)
(******************************************************************************)
Init ==
    /\ state = InitState    \* state is at the initial state, and 
    /\ index = 1            \* note that sequence index starts from 1, not 0
    /\ chain = <<>>         \* empty transaction queue.

----
(******************************************************************************)
(* Actions                                                                    *)
(******************************************************************************)

(******************************************************************************)
(* SubmitTX: Client appends a transaction to the transaction queue.           *)
(******************************************************************************)
SubmitTX(tx) ==
    /\ tx \in TX \* TX type check
    /\ chain' = Append(chain, [tx |-> tx, is_valid |-> NULL])
    /\ UNCHANGED <<state, index>> 


(******************************************************************************)
(* ProcessTx: Ledger processes the oldest unprocessed TX and updates its      *)
(* state by applyinng f                                                       *)
(******************************************************************************)
ProcessTX_OK ==
    LET
        f == chain[index].tx.f
    IN
        /\ index \in DOMAIN chain
        /\ chain' = [chain EXCEPT ![index].is_valid = TRUE]  \* update validity flag
        /\ index' = index + 1   \* increment the index.
        /\ state' \in f[state]  \* perform non-deterministic state transition by f.
        
ProcessTX_ERR ==
    LET
        f == chain[index].tx.f
    IN
        /\ index \in DOMAIN chain
        /\ chain' = [chain EXCEPT ![index].is_valid = FALSE]  \* see above.
        /\ index' = index + 1  \* see above.
        /\ UNCHANGED state     \* state does not change due to invalid TX.

Next == (\E tx: SubmitTX(tx)) \/ ProcessTX_OK \/ ProcessTX_ERR

(******************************************************************************)
(* Specification                                                              *)
(******************************************************************************)    
Spec == Init /\ [][Next]_vars

(******************************************************************************)
(* Unconditional Induction Lemma                                              *)
(******************************************************************************)
LEMMA SpecInduction == 
    ASSUME
        NEW Invariant,
        ASSUME Init PROVE Invariant,
        ASSUME Invariant, NEW tx, SubmitTX(tx) PROVE Invariant',
        ASSUME Invariant, ProcessTX_OK PROVE Invariant',
        ASSUME Invariant, ProcessTX_ERR PROVE Invariant'
    PROVE
        Spec => []Invariant
PROOF
    <1>1. Init => Invariant OBVIOUS
    <1>2. Invariant /\ Next => Invariant' OBVIOUS
    <1>3. Invariant /\ UNCHANGED vars => Invariant' OBVIOUS
    <1> QED BY PTL, <1>1, <1>2, <1>3 DEF Spec
    
----
(******************************************************************************)
(* Invariants                                                                 *)
(******************************************************************************)

(******************************************************************************)
(*  Type invariant                                                            *)
(******************************************************************************)
TypeInv ==
    /\ state \in State
    /\ (index \in Nat /\ index > 0)
    /\ chain \in Chain

\* Invariant (safety) on the blockchain
ChainInv ==
    \* chain = (processed part) + (unprocessed part) 
    /\ \A i \in 1 .. index-1: chain[i].is_valid \in BOOLEAN
    /\ \A i \in {i \in Nat: index <= i} \cap DOMAIN chain: chain[i].is_valid = NULL

Inv == TypeInv /\ ChainInv

(* Type safety (invariant) proof that use the induction lemma above *)
THEOREM TypeSafety == Spec => []TypeInv
PROOF
(*
    <1>1. ASSUME Init PROVE TypeInv OMITTED
    <1>2. ASSUME TypeInv, NEW tx, SubmitTX(tx) PROVE TypeInv' OMITTED
    <1>3. ASSUME TypeInv, ProcessTX_OK PROVE TypeInv' OMITTED
    <1>4. ASSUME TypeInv, ProcessTX_ERR PROVE TypeInv' OMITTED
*)
    <1>1. Init => TypeInv
        <2>1. SUFFICES ASSUME Init PROVE TypeInv OBVIOUS
        <2> QED OMITTED
    <1>2. TypeInv /\ \E tx: SubmitTX(tx) => TypeInv'
        <2>1. SUFFICES ASSUME TypeInv, NEW tx, SubmitTX(tx) PROVE TypeInv' OBVIOUS
        <2> QED OMITTED
    <1>3. TypeInv /\ ProcessTX_OK => TypeInv'
        <2>1. SUFFICES ASSUME TypeInv, ProcessTX_OK PROVE TypeInv' OBVIOUS
        <2> QED OMITTED
    <1>4. TypeInv /\ ProcessTX_ERR => TypeInv'
        <2>1. SUFFICES ASSUME TypeInv, ProcessTX_ERR PROVE TypeInv' OBVIOUS
        <2> QED OMITTED
    <1> QED BY PTL, <1>1, <1>2, <1>3, <1>4 DEF Spec, Next

(* Invariant (safety) on the high-level Ledger *) 
THEOREM LedgerInv == Spec => []Inv
PROOF
    <1>1 Init => Inv
        BY InitStateAxiom DEF Init, Inv, TypeInv, ChainInv, Chain
    <1>2 Inv /\ [Next]_vars => Inv'
        <2>1 SUFFICES ASSUME TypeInv, ChainInv, [Next]_vars PROVE Inv' BY DEF Inv
        <2>2 CASE Next
            <3> USE DEF Inv, Next
            <3> USE DEF TypeInv, ChainInv, Chain, ChainEntry
            <3>1 CASE (\E tx \in TX: SubmitTX(tx))
                <4> USE DEF SubmitTX
                <4>a \A i \in DOMAIN chain: chain[i] = chain'[i] BY <3>1 
                <4>1 TypeInv' BY <2>1, <3>1
                <4>2 ChainInv'
                    <5>1 ChainInv!1' OBVIOUS
                    <5>2 ChainInv!2' 
                        <6>a DOMAIN chain' = DOMAIN chain \union { Len(chain)+1 } BY TypeInv, <3>1
                        <6>1 PICK tx \in TX: SubmitTX(tx) BY <3>1
                        <6>2 TAKE i \in ({i \in Nat: index <= i} \cap DOMAIN chain)'
                        <6>3 CASE i \in ({j \in Nat: index <= j} \cap { Len(chain)+1 }) BY <2>1, <4>a, <6>1, <6>3
                        <6>4 CASE i \in ({j \in Nat: index <= j} \cap DOMAIN chain) BY <2>1, <4>a, <6>1, <6>4
                        <6> QED BY <2>1, <6>a, <6>1, <6>2, <6>3, <6>4 
                    <5> QED BY <5>1, <5>2
                <4> QED BY <4>1, <4>2
            <3>2 CASE ProcessTX_OK
                <4> USE DEF ProcessTX_OK
                <4>1 TypeInv' BY <2>1, <3>2 DEF TX, Operation, TotalFunc
                <4>2 ChainInv'
                    <5> ChainInv!1' OBVIOUS
                    <5> ChainInv!2' BY <2>1, <3>2
                    <5> QED OBVIOUS
                <4> QED BY <4>1, <4>2
            <3>3 CASE ProcessTX_ERR
                <4> USE DEF ProcessTX_ERR
                <4>1 TypeInv' BY <2>1, <2>2, <3>3 DEF TX, Operation, TotalFunc
                <4>2 ChainInv'
                    <5> ChainInv!1' OBVIOUS
                    <5> ChainInv!2' BY <2>1, <3>3
                    <5> QED OBVIOUS
                <4> QED BY <4>1, <4>2
            <3> QED
                BY <2>1, <2>2, <3>1, <3>2, <3>3
        <2>3 CASE UNCHANGED vars
            BY <2>1, <2>3 DEF Inv, TypeInv, ChainInv, vars
        <2> QED BY <2>1, <2>2, <2>3
    <1> QED BY PTL, <1>1, <1>2 DEF Spec
  
================================================================================
\* Modification History
\* Last modified Fri Jul 26 10:40:46 JST 2019 by shinsa
\* Created Fri Jun 07 01:51:28 JST 2019 by shinsa
