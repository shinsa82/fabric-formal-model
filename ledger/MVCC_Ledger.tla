------------------------------ MODULE MVCC_Ledger ------------------------------
(******************************************************************************)
(* High level specification of DLT Ledger,                                     *)
(* expressed as a single state machine without MVCC validation                                      *)
(******************************************************************************)

EXTENDS Sequences, Integers, TLAPS

CONSTANTS State, InitState \* Set of states and 
ASSUME InitState \in State \* Designated initial state

CONSTANTS RWSet, diff(_,_,_) \* read-write set, which is a result of a simulation, is introduced in this version.

(******************************************************************************)
(* State variables of this module                                             *)
(******************************************************************************)
VARIABLE state \* current state of the ledger state machine
VARIABLE transactions \* list of accepted transactions 

(* Operation is a function from a state to a state, can be non-deterministic, but required to be total. *)   
Operation == SUBSET [State -> (SUBSET State) \ {}]
\* Operation == { f \in [State -> SUBSET State]: \A s \in State: \E s1 \in State: s1 \in f[s] }
TX == [f: Operation] \* transaction record. note that "f" is just a label


\* the following does not work... so I put the condition into the definition of Operartion set
\* ASSUME \A f \in Operation, s \in State: \E s1 \in State: s1 \in f[s] \* f is total
 
 
(******************************************************************************)
(*  Type invariant                                                            *)
(******************************************************************************)
TypeInvariant ==
    /\ state \in State
    \* For each TX in the queue, it has a flag is it's processed or not 
    /\ transactions \in Seq([tx: TX, rwset: RWSet, processed: BOOLEAN])
 
----
(******************************************************************************)
(* Initial condition                                                          *)
(******************************************************************************)
Init ==
    /\ state = InitState   \* state is at the initial state, and 
    /\ transactions = <<>> \* empty transaction queue.

----
(******************************************************************************)
(* Actions                                                                    *)
(******************************************************************************)

(******************************************************************************)
(* (non-deterministic) simulaton result for the operation f                   *)
(******************************************************************************)
simulate(f) == { rwset \in RWSet: \E post_state \in f[state]: diff(state, post_state, rwset) }

(******************************************************************************)
(* SubmitTx: A client appends a transaction and its simulation result to the  *)
(* transaction queue.                                                         *)
(******************************************************************************)
SubmitTx(tx) ==
    /\ \E rs \in simulate(tx.f):
        transactions' = Append(transactions, [tx |-> tx, rwset |-> rs, processed |-> FALSE])
    /\ UNCHANGED state 

(******************************************************************************)
(* CommitTx: Ledger processes the oldest unprocessed TX and                      *)
(******************************************************************************)
CONSTANTS apply(_, _) \* Applies rwset to the current state

commitSub(idx) ==
    (* changes ledger's state by the transaction at index idx *)
    LET
        cur_tx == transactions[idx].tx
        rwset == transactions[idx].rwset
        f == cur_tx.f
    IN
        /\ transactions' = [transactions EXCEPT ![idx].processed = TRUE] \* updates processed flag
        /\
            \/ state' = apply(state, rwset) \* perform state transition, which is non-deterministic 
            \/ UNCHANGED state     \* or state does not change (by TX failure)

CommitTx ==
    \E idx \in 1..Len(transactions):
        \* idx is the smallest index where TX is not processed 
        /\ \A j \in 1..idx-1: transactions[j].processed = TRUE 
        /\ \A k \in idx..Len(transactions): transactions[k].processed = FALSE
        /\ commitSub(idx) \* process idx-th item

Next == (\E tx \in TX: SubmitTx(tx)) \/ CommitTx

(******************************************************************************)
(* Specification                                                              *)
(******************************************************************************)    
Spec == Init /\ [][Next]_<<state, transactions>>

----
(******************************************************************************)
(* Invariants                                                                 *)
(******************************************************************************)
Finality == TRUE \* TODO
Safety == Finality

Invariant ==
    /\ TypeInvariant
    /\ Len(transactions) > 0 => \E idx \in 1..Len(transactions)+1: 
        /\ \A j \in 1..idx-1: transactions[j].processed = TRUE
        /\ \A k \in idx..Len(transactions): transactions[k].processed = FALSE
    
THEOREM Spec => []Invariant

LedgerSpec(_state, _transactions) == INSTANCE Ledger WITH state <- _state, transactions <- _transactions

\* ideal form
THEOREM Spec => \EE ex_state, ex_txs: LedgerSpec(ex_state, ex_txs)!Spec
    OMITTED

(******************************************************************************)
(* Refinement Mapping                                                         *)
(******************************************************************************)
h_state == state \* ad hoc impl
(*
h_txs ==  CHOOSE seq \in Seq([tx: TX, processed: BOOLEAN]):
    /\ Len(seq) = Len(transactions)
    /\ \A i \in 1..Len(seq):
        /\ seq[i].tx = transactions[i].tx
        /\ seq[i].processed = transactions[i].processed
*)
h_txs == transactions \* ad hoc impl

LEMMA L1 == transactions = <<>> => h_txs = <<>>
    BY DEF h_txs

(******************************************************************************)
(* Refinement Theorem                                                         *)
(******************************************************************************)
THEOREM Spec => LedgerSpec(h_state, h_txs)!Spec
<1> USE DEF Spec, LedgerSpec!Spec, h_state, h_txs
<1>1. Init => LedgerSpec(h_state, h_txs)!Init
    BY DEF Init, LedgerSpec!Init
<1>2. Next =>
    \/ LedgerSpec(h_state, h_txs)!Next
    \/ UNCHANGED <<h_state, h_txs>>
    <2>1. (\E tx \in TX: SubmitTx(tx)) =>
        \/ LedgerSpec(h_state, h_txs)!Next
        <3>1. (\E tx \in TX: SubmitTx(tx)) => 
            (\E tx \in LedgerSpec(h_state, h_txs)!TX: LedgerSpec(h_state, h_txs)!SubmitTx(tx))
            OMITTED
        \* (\E tx \in LedgerSpec(h_state, h_txs)!TX: LedgerSpec(h_state, h_txs)!SubmitTx(tx))
        <3>2. QED 
            BY <3>1 DEF LedgerSpec!Next
    <2>2. CommitTx => 
        \/ LedgerSpec(h_state, h_txs)!Next
        \/ UNCHANGED <<h_state, h_txs>>
        <3>1. CommitTx => 
            \/ LedgerSpec(h_state, h_txs)!CommitTx
            \/ UNCHANGED <<h_state, h_txs>>
            OMITTED
        <3>2. QED
            BY <3>1 DEF LedgerSpec!Next
    <2>3. QED
        BY <2>1, <2>2 DEF Next
<1>3. UNCHANGED <<state, transactions>> =>
    \/ UNCHANGED <<h_state, h_txs>>
    OBVIOUS
<1>4. QED
    BY PTL, <1>1, <1>2

================================================================================
\* Modification History
\* Last modified Wed Jul 03 15:52:00 JST 2019 by shinsa
\* Created Tue Jul 02 01:10:01 JST 2019 by shinsa
