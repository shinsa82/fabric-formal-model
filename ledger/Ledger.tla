-------------------------------- MODULE Ledger --------------------------------
(******************************************************************************)
(* High level specification of DLT Ledger,                                     *)
(* expressed as a single state machine without MVCC validation                                      *)
(******************************************************************************)
EXTENDS Sequences, Integers, TLAPS

(******************************************************************************)
(* Constants                                                                  *)
(******************************************************************************)
CONSTANTS State, InitState \* a set of states, and 
ASSUME InitStateAxiom == InitState \in State \* the designated initial state.
NULL == CHOOSE x : x \notin BOOLEAN 

(******************************************************************************)
(* State variables of this module                                             *)
(******************************************************************************)
VARIABLES state,    \* current state of the ledger state machine.
          chain,    \* blockchain, a list of received transactions. 
          index     \* index of the blockchain.
vars == <<state, chain, index>>

(******************************************************************************)
(* Datatype definition                                                        *)
(******************************************************************************)

TotalFunc(S1, S2) == [ S1 -> S2 \ {{}} ]\* a set of total function from S1 to S2 

(******************************************************************************)
(* Operation is a function from a state to a state, can be non-deterministic, *)
(* but required to be total.                                                  *)
(******************************************************************************)   
Operation == TotalFunc(State, SUBSET State)
\*Operation == [State -> (SUBSET State) \ {{}}]

TX == [f: Operation] \* a transaction. note that "f" is just a label
 
(******************************************************************************)
(*  Type invariant                                                            *)
(******************************************************************************)
ChainEntry == [tx: TX, is_valid: BOOLEAN \union {NULL}] 
Chain == Seq(ChainEntry)
TypeInv ==
    /\ state \in State
    /\ index \in Nat
    /\ index > 0
    \* Each TX in the blockchain has a flag if it's valid or not. Before the TX is processed, its value is NULL.
    /\ chain \in Chain
----
(******************************************************************************)
(* Initial condition                                                          *)
(******************************************************************************)
Init ==
    /\ state = InitState    \* state is at the initial state, and 
    /\ index = 1
    /\ chain = <<>>         \* empty transaction queue.

----
(******************************************************************************)
(* Actions                                                                    *)
(******************************************************************************)

(******************************************************************************)
(* SubmitTX: A client appends a transaction to the transaction queue.                            *)
(******************************************************************************)
SubmitTX(tx) ==
    /\ chain' = Append(chain, [tx |-> tx, is_valid |-> NULL])
    /\ UNCHANGED <<state, index>> 

(******************************************************************************)
(* CommitTx: Ledger processes the oldest unprocessed TX and                   *)
(******************************************************************************)
ProcessTX_OK ==
    LET
        f == chain[index].tx.f
    IN
        /\ Len(chain) >= index
        /\ chain' = [chain EXCEPT ![index].is_valid = TRUE]  \* update validity flag
        /\ index' = index + 1   \* increment the index.
        /\ state' \in f[state]  \* perform non-deterministic state transition by f.
        
ProcessTX_ERR ==
    LET
        f == chain[index].tx.f
    IN
        /\ Len(chain) >= index
        /\ chain' = [chain EXCEPT ![index].is_valid = FALSE]  \* see above.
        /\ index' = index + 1  \* see above.
        /\ UNCHANGED state     \* state does not change due to invalid TX.

Next == (\E tx \in TX: SubmitTX(tx)) \/ ProcessTX_OK \/ ProcessTX_ERR

(******************************************************************************)
(* Specification                                                              *)
(******************************************************************************)    
Spec == Init /\ [][Next]_vars

----
(******************************************************************************)
(* Invariants                                                                 *)
(******************************************************************************)
Finality == TRUE \* TODO
Safety == Finality

\* Invariant (safety) on teh blockchain
ChainInv == TRUE
\*    /\ Len(chain) > 0 => \E idx \in 1..Len(chain)+1: 
\*        /\ \A j \in 1..idx-1: chain[j].processed = TRUE
\*        /\ \A k \in idx..Len(chain): chain[k].processed = FALSE

Inv == TypeInv /\ ChainInv

THEOREM LedgerInv == Spec => []Inv
PROOF
    <1>1 Init => Inv
        BY InitStateAxiom DEF Init, Inv, TypeInv, ChainInv, Chain
    <1>2 Inv /\ [Next]_vars => Inv'
        <2>1 SUFFICES ASSUME TypeInv, ChainInv, [Next]_vars PROVE Inv' BY DEF Inv
        <2>2 CASE Next
            <3> USE DEF Inv, Next
            <3>0 ChainInv' BY DEF ChainInv
            <3>1 TypeInv'
                <4> USE DEF TypeInv, Chain, ChainEntry
                <4>1 CASE (\E tx \in TX: SubmitTX(tx))
                    BY <2>1, <2>2, <4>1 DEF SubmitTX
                <4>2 CASE ProcessTX_OK
                    BY ONLY <2>1, <2>2, <4>2 DEF ProcessTX_OK, TX, Operation, TotalFunc   
                <4>3 CASE ProcessTX_ERR 
                    BY <2>1, <2>2, <4>3 DEF ProcessTX_ERR
                <4> QED BY <2>1, <2>2, <4>1, <4>2, <4>3
            <3> QED BY <2>1, <2>2, <3>0, <3>1
        <2>3 CASE UNCHANGED vars
            BY <2>1, <2>3 DEF Inv, TypeInv, ChainInv, vars
        <2> QED BY <2>1, <2>2, <2>3
    <1> QED BY PTL, <1>1, <1>2 DEF Spec

(*    
THEOREM TypeSafety == Spec => []TypeInvariant
    <1>1 Init => TypeInvariant
        BY InitStateAxiom DEF Init, TypeInvariant, Chain
    <1>2 TypeInvariant /\ [Next]_<<state, index, chain>> => TypeInvariant'
        <2> SUFFICES ASSUME TypeInvariant,  [Next]_<<state, index, chain>> PROVE TypeInvariant'
            OBVIOUS
        <2>2. CASE Next
            <3> SUFFICES ASSUME TypeInvariant, Next PROVE TypeInvariant'
                BY <2>2
            <3>2. QED
                <4>1. CASE (\E tx \in TX: SubmitTX(tx))
                    <5>1. SUFFICES ASSUME TypeInvariant, (\E tx \in TX: SubmitTX(tx)) PROVE TypeInvariant'
                        BY <4>1
                    <5> QED
                        BY ONLY <5>1 DEF SubmitTX, TypeInvariant, Chain, ChainEntry
                <4>2. CASE ProcessTX
                    <5> USE DEF TypeInvariant, ProcessTX
                    <5>1. SUFFICES ASSUME TypeInvariant, Len(chain) >= index, ProcessTX_OK \/ ProcessTX_ERR PROVE TypeInvariant'
                        BY <4>2
                    <5>2. ASSUME TypeInvariant, Len(chain) >= index, ProcessTX_OK PROVE TypeInvariant'
                        <6> USE DEF ProcessTX_OK, Chain, ChainEntry
                        <6>0. state' \in State
                            BY <5>2, chain[index] \in ChainEntry, chain[index].tx \in TX DEF TX, Operation, TotalFunc
                        <6>1. index' \in Nat
                            BY <5>2
                        <6>2. index' > 0
                            BY <5>2
                        <6>3. chain' \in Chain
                            BY <5>2
                        <6> QED
                            BY <6>0, <6>1, <6>2, <6>3
                    <5>3. ASSUME TypeInvariant, Len(chain) >= index, ProcessTX_ERR PROVE TypeInvariant'
                        BY <5>3 DEF ProcessTX_ERR, Chain, ChainEntry
                    <5> QED
                        BY ONLY <5>1, <5>2, <5>3 DEF ProcessTX, TypeInvariant
                <4> QED
                    BY <4>1, <4>2 DEF Next, TypeInvariant
        <2>3 CASE UNCHANGED <<state, index, chain>>
            <3>1. SUFFICES ASSUME TypeInvariant, UNCHANGED <<state, index, chain>> PROVE TypeInvariant'
                BY <2>3
            <3>2. QED
                BY <2>3 DEF TypeInvariant
        <2> QED BY <2>2, <2>3
    <1> QED BY PTL, <1>1, <1>2 DEF Spec
*)    
================================================================================
\* Modification History
\* Last modified Sat Jul 06 12:13:16 JST 2019 by shinsa
\* Created Fri Jun 07 01:51:28 JST 2019 by shinsa
