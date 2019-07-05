------------------------------ MODULE LedgerSpec ------------------------------
(******************************************************************************)
(* High level specification of DLT Ledger                                     *)
(* Single state machine and no MVCC                                           *)
(******************************************************************************)
EXTENDS Sequences, Integers

CONSTANTS State, InitState
VARIABLES state, transactions

ASSUME InitState \in State
ASSUME \A f, s0: \E s1: s1 \in f[s0] \* f is total
 
Init ==
    /\ state = InitState 
    /\ transactions = <<>>

(******************************************************************************)
(* Actions                                                                    *)
(******************************************************************************)
 
SubmitTx(tx) == transactions' = Append(transactions, [tx |-> tx, processed |-> FALSE]) 

commitSub(idx) ==
    LET
        tx == transactions[idx]
        f == tx.f
    IN
        /\ transactions' = [transactions EXCEPT ![idx].processed = TRUE]
        /\
            \/ state' = CHOOSE s: f[state]
            \/ UNCHANGED state

CommitTx ==  \E idx:
    /\ \A j \in 1..idx-1: transactions[j].processed = TRUE
    /\ \A j \in idx..Len(transactions): transactions[j].processed = FALSE
    /\ commitSub(idx)


Next == (\E tx: SubmitTx(tx)) \/ CommitTx

(******************************************************************************)
(* Specification                                                              *)
(******************************************************************************)    

Spec == Init /\ [][Next]_<<state, transactions>>

----
(******************************************************************************)
(* Invariants                                                                 *)
(******************************************************************************)

Invariant ==
    /\ state \in State

THEOREM Spec => []Invariant
================================================================================
\* Modification History
\* Last modified Fri Jun 07 12:44:09 JST 2019 by shinsa
\* Created Fri Jun 07 01:51:28 JST 2019 by shinsa
