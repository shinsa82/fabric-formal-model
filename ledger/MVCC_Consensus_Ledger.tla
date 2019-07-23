------------------------- MODULE MVCC_Consensus_Ledger -------------------------
(******************************************************************************)
(* Low-level specification of DLT Ledger,                                     *)
(* which handles multiple Endorsement with MVCC validation                    *)
(******************************************************************************)
EXTENDS Sequences, SequenceTheorems, Integers, TLAPS, Datatype

(******************************************************************************)
(* Read-write set, which is a result of a simulation                          *)
(******************************************************************************)
CONSTANTS RWSet

(******************************************************************************)
(* State variables of this module                                             *)
(******************************************************************************)
VARIABLES state,    \* current state of the ledger state machine.
          chain,    \* blockchain, a list of received transactions. 
          index     \* unprocessed TX index at the blockchain.
vars == <<state, chain, index>>

(******************************************************************************)
(*  Type invariant                                                            *)
(******************************************************************************)

(******************************************************************************)
(* At this module, endorsement is a sequence of RWSets                        *)
(******************************************************************************)
Endorsement == Seq(RWSet) 

\* each entry of blockchain now has a RWSet.
ChainEntry == [tx: TX, endorsement: Endorsement, is_valid: BOOLEAN \union {NULL}] 
Chain == Seq(ChainEntry)
TypeInv ==
    /\ state \in State
    /\ index \in Nat
    /\ index > 0
    \* Each TX in the blockchain has a flag if it's valid or not. Before the TX
    \* is processed, its value is NULL.
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
(* (non-deterministic) simulaton result for the operation f                   *)
(******************************************************************************)
CONSTANT SameOnRSet(_, _), Commit(_, _)
ASSUME SameOnRSetAxiom == \A s \in State, rwset \in RWSet: SameOnRSet(s, rwset) \in BOOLEAN  
ASSUME CommitAxiom == \A s \in State, rwset \in RWSet: Commit(s, rwset) \in State  

simulate(s, f) == CHOOSE rwset \in RWSet:
    (\A ss \in State: SameOnRSet(ss, rwset) => Commit(ss, rwset) \in f[s])
ASSUME simulateAxiom == \A s \in State, f \in Operation:
    \E rwset \in RWSet:
        (\A ss \in State: SameOnRSet(ss, rwset) => Commit(ss, rwset) \in f[s])
LEMMA L1 == \A s \in State, f \in Operation: simulate(s, f) \in RWSet
PROOF
    <1> TAKE s \in State, f \in Operation
    <1> QED
        BY simulateAxiom DEF simulate

endorsement(tx) == simulate(state, tx.f) 

(******************************************************************************)
(* SubmitTx: Client appends a transaction and its simulation result to the    *)
(* transaction queue.                                                         *)
(******************************************************************************)
SubmitTX(tx) ==
    LET
        total == 4

        \* 0 = normal, 1 = unreachable, 2 = faulty
        flags == CHOOSE fs \in [1..total -> 0..2]: Len(SelectSeq(fs, LAMBDA i: fs[i] = 2)) <= 1 

        end == [i \in 1..total |-> 
            IF i=0 THEN endorsement(tx)
            ELSE (IF i=1 THEN NULL ELSE CHOOSE rw \in RWSet: TRUE)]

    IN
        /\ chain' = Append(chain, [tx |-> tx, endorsement |-> end, is_valid |-> NULL])
        /\ UNCHANGED <<state, index>> 

(******************************************************************************)
(* ProcessTx: Ledger processes the oldest unprocessed TX and updates its      *)
(* state by committing RWSet of f                                             *)
(******************************************************************************)
ProcessTX_OK ==
    LET
        f == chain[index].tx.f
        rwset == chain[index].endorsement
    IN
        \* /\ Len(chain) >= index
        /\ index \in DOMAIN chain
        /\ SameOnRSet(state, rwset)
        /\ chain' = [chain EXCEPT ![index].is_valid = TRUE]  \* update validity flag
        /\ index' = index + 1   \* increment the index.
        /\ state' = Commit(state, rwset)  \* perform non-deterministic state transition by rwset.
        
ProcessTX_ERR ==
    LET
        f == chain[index].tx.f
        rwset == chain[index].endorsement
    IN
        \* /\ Len(chain) >= index
        /\ index \in DOMAIN chain
        /\ ~SameOnRSet(state, rwset)
        /\ chain' = [chain EXCEPT ![index].is_valid = FALSE]  \* see above.
        /\ index' = index + 1  \* see above.
        /\ UNCHANGED state     \* state does not change due to invalid TX.

Next == (\E tx \in TX: SubmitTX(tx)) \/ ProcessTX_OK \/ ProcessTX_ERR

(******************************************************************************)
(* Specification                                                              *)
(******************************************************************************)    
Spec == Init /\ [][Next]_vars


================================================================================
\* Modification History
\* Last modified Tue Jul 23 12:57:16 JST 2019 by shinsa
\* Created Tue Jul 23 12:40:58 JST 2019 by shinsa
