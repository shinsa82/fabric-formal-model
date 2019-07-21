------------------------------ MODULE MVCC_Ledger ------------------------------
(******************************************************************************)
(* Middle level specification of DLT Ledger,                                  *)
(* expressed as a single state machine with MVCC validation                   *)
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
(* At this module, endorsement is just a RWSet, which will be extended at     *)
(* lower models.                                                              *)
(******************************************************************************)
Endorsement == RWSet 

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
        end == endorsement(tx)
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

----
(******************************************************************************)
(* Invariants                                                                 *)
(******************************************************************************)
Finality == TRUE \* TODO
Safety == Finality

\* Invariant (safety) on the blockchain
ChainInv ==
    \* chain = (processed part) + (unprocessed part) 
    /\ \A i \in 1 .. index-1: chain[i].is_valid \in BOOLEAN
    /\ \A i \in {i \in Nat: index <= i} \cap DOMAIN chain: chain[i].is_valid = NULL

Inv == TypeInv /\ ChainInv
    
(* Invariant (safety) on the MVCC Ledger *) 
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
                <4>1 TypeInv' BY <2>1, <3>1, L1 DEF endorsement, Endorsement
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

(*

\* ideal form
THEOREM Spec => \EE ex_state, ex_txs: LedgerSpec(ex_state, ex_txs)!Spec
    OMITTED
*)

(******************************************************************************)
(* Refinement Mapping                                                         *)
(******************************************************************************)
(*
VARIABLES h_state,
          h_chain,
          h_index 
*)

fmap(f(_), seq) == [ i \in DOMAIN seq |-> f(seq[i]) ]
proj(r) == [ tx |-> r.tx, is_valid |-> r.is_valid ]
Proj(seq) == fmap(proj, seq)

h_state == state
h_chain == Proj(chain)
h_index == index
h_vars == <<h_state, h_chain, h_index>>

HSpec == 
    INSTANCE Ledger WITH state <- h_state, chain <- h_chain, index <- h_index

AXIOM NullEquality == NULL = HSpec!NULL
LEMMA TypeEquality == Operation = HSpec!Operation /\ TX = HSpec!TX /\ NULL = HSpec!NULL
PROOF
    BY NullEquality DEF TX, HSpec!TX, Operation, HSpec!Operation, TotalFunc, HSpec!TotalFunc

LEMMA fmapProperties ==
    ASSUME
        NEW S, NEW T, NEW f(_),
        NEW seq \in Seq(S),
        ASSUME NEW e \in S PROVE f(e) \in T
    PROVE
        /\ fmap(f, seq) \in Seq(T)
        /\ Len(fmap(f,seq)) = Len(seq)
PROOF 
    <1> DEFINE lhs == fmap(f, seq)
    <1>1. fmap(f, seq) \in Seq(T)
        <2>1. \A i \in DOMAIN lhs: lhs[i] \in T
            <3> TAKE i \in DOMAIN lhs
            <3>1. lhs[i] \in T BY DEF fmap
            <3> QED BY <3>1
        <2> QED BY <2>1, LenProperties, IsASeq DEF fmap
    <1>2. Len(fmap(f,seq)) = Len(seq) BY DEF fmap
    <1> QED BY <1>1, <1>2
    
LEMMA projProperties ==
    ASSUME NEW ce \in ChainEntry PROVE proj(ce) \in HSpec!ChainEntry
        BY TypeEquality DEF ChainEntry, HSpec!ChainEntry, proj

LEMMA ProjProperties ==
    ASSUME NEW es \in Seq(ChainEntry)
    PROVE
        /\ Proj(es) \in Seq(HSpec!ChainEntry)
        /\ Len(es) = Len(Proj(es))
PROOF
    <1>1. Proj(es) \in Seq(HSpec!ChainEntry)
        BY fmapProperties, projProperties DEF Proj
    <1>2. Len(Proj(es)) = Len(es)
        BY fmapProperties, projProperties DEF Proj
    <1> QED BY <1>1, <1>2
    
LEMMA L2 ==
    /\ DOMAIN chain = DOMAIN h_chain
    /\ \A i \in DOMAIN h_chain:
        h_chain[i].tx = chain[i].tx /\ h_chain[i].is_valid = chain[i].is_valid 
    BY DEF h_chain, proj

LEMMA L3 == 
    ASSUME
        NEW S, NEW T, NEW f(_),
        NEW e \in S, NEW seq \in Seq(S),
        ASSUME NEW e0 \in S PROVE f(e0) \in T
    PROVE fmap(f, Append(seq, e)) = Append(fmap(f, seq), f(e))
PROOF
    <1>1. DEFINE lhs == fmap(f, Append(seq, e))
    <1>2. DEFINE rhs == Append(fmap(f, seq), f(e))
    <1>3. lhs \in Seq(T) BY DEF fmap
    <1>4. rhs \in Seq(T) BY fmapProperties
    <1>5. Len(fmap(f,seq)) = Len(seq) BY DEF fmap
    <1>6. Len(rhs) = Len(seq) + 1 BY <1>5
    <1>7. Len(lhs) = Len(seq) + 1 BY <1>5 DEF fmap
    <1>8. Len(lhs) = Len(rhs) BY <1>6, <1>7
    <1> HIDE DEF lhs, rhs
    <1>9. \A i \in 1..Len(lhs): lhs[i] = rhs[i]
        <2>1. TAKE i \in 1..Len(lhs)
        <2>2. lhs[i] = f(Append(seq,e)[i]) BY DEF lhs, fmap
        <2>3. CASE i \in 1..Len(seq)
            <3>1. f(Append(seq,e)[i]) = f(seq[i]) BY <2>3 DEF lhs
            <3>2. rhs[i] = fmap(f,seq)[i]
                BY AppendProperties, <2>3, i \in 1..Len(fmap(f,seq)) DEF rhs, fmap
            <3>3. fmap(f,seq)[i] = f(seq[i]) BY <2>3, LenProperties, i \in DOMAIN seq DEF fmap
            <3> QED BY <2>2, <3>1, <3>2, <3>3 DEF lhs, rhs, fmap
        <2>4. CASE i = Len(seq)+1
            <3>1. f(Append(seq,e)[i]) = f(e) BY <2>4, AppendProperties
            <3>2. i = Len(fmap(f,seq)) + 1 BY <1>5, <2>4, AppendProperties DEF rhs
            <3>3. rhs[i] = f(e) BY <3>2, AppendProperties DEF rhs, fmap
            <3> QED BY <2>2, <3>1, <3>3 DEF lhs, rhs 
        <2> QED BY <1>7, <2>3, <2>4
    <1> QED BY <1>3, <1>4, <1>8, <1>9, SeqEqual DEF lhs, rhs

    
LEMMA L4 ==
    ASSUME
        NEW e \in ChainEntry,
        NEW seq \in Seq(ChainEntry)
    PROVE
        Proj(Append(seq, e)) = Append(Proj(seq), proj(e))
PROOF
    <1>1 ASSUME
            NEW e1 \in ChainEntry,
            NEW seq1 \in Seq(ChainEntry),
            ASSUME NEW e0 \in ChainEntry PROVE proj(e0) \in HSpec!ChainEntry
         PROVE
            Proj(Append(seq1, e1)) = Append(Proj(seq1), proj(e1))
         BY projProperties, L3 DEF Proj
    <1> QED BY <1>1, projProperties
    
(******************************************************************************)
(* Refinement Theorem                                                         *)
(******************************************************************************)
THEOREM Refinement == Spec => HSpec!Spec
PROOF
    <1> USE DEF Spec, HSpec!Spec, vars, HSpec!vars, proj
    \* init case
    <1>1. Init => HSpec!Init
        BY DEF Init, HSpec!Init, h_state, h_chain, h_index, Proj, fmap
    \* next step (progress)
    <1>2. Next => HSpec!Next \/ UNCHANGED HSpec!vars
        \* <2>0. ASSUME Next PROVE TypeInv BY LedgerInv DEF PTL, Spec, Inv
        <2>1. CASE \E tx \in TX: SubmitTX(tx)
            <3>1. PICK tx0 \in TX: SubmitTX(tx0) BY <2>1
            <3>3. \E tx \in HSpec!TX: HSpec!SubmitTX(tx)
                <4> USE TypeEquality
                <4>1. WITNESS tx0 \in HSpec!TX
                <4>3. HSpec!SubmitTX(tx0)!1
                    <5>1. DEFINE e == [tx |-> tx0, endorsement |-> endorsement(tx0), is_valid |-> NULL]
                    <5>c. chain \in Seq(ChainEntry) OMITTED
                    <5>a. e \in ChainEntry OMITTED
                    <5>b. proj(e) = [tx |-> tx0, is_valid |-> HSpec!NULL] BY TypeEquality
                    <5> HIDE DEF e, proj
                    <5>k. Proj(Append(chain, e)) = Append(Proj(chain), proj(e))
                        BY <5>c, <5>a, <5>b, L4 DEF h_chain
                    <5> QED BY <3>1, Proj(chain)' = Proj(Append(chain, e)), <5>k, <5>b DEF SubmitTX, h_chain, e
                <4> QED BY <3>1, <4>3 DEF SubmitTX, HSpec!SubmitTX, h_index, h_state
            <3> QED 
                BY <2>1, <3>3 DEF HSpec!Next
        <2>2. ProcessTX_OK => HSpec!Next \/ UNCHANGED HSpec!vars
            <3>1. ProcessTX_OK=> 
            \/ HSpec!ProcessTX_OK
            \/ UNCHANGED HSpec!vars
                <4>1. HSpec!ProcessTX_OK OMITTED
                <4> QED BY <4>1
            <3>2. QED
                BY <3>1 DEF HSpec!Next
        <2>3. ProcessTX_ERR => HSpec!Next \/ UNCHANGED HSpec!vars
            <3> USE DEF HSpec!Next, ProcessTX_ERR, HSpec!ProcessTX_ERR
            <3>1. ASSUME ProcessTX_ERR PROVE HSpec!ProcessTX_ERR
                <4>1. h_index \in DOMAIN h_chain
                    <5>a. chain \in Seq(ChainEntry) OMITTED
                    <5>1. DOMAIN chain = DOMAIN Proj(chain) BY <5>a, ProjProperties
                    <5> QED BY <3>1, <5>1, ProjProperties DEF h_index, h_chain
                <4>3. h_chain' = [h_chain EXCEPT ![h_index].is_valid = FALSE]
                    <5> DEFINE lhs == Proj(chain)'
                    <5> DEFINE rhs == [Proj(chain) EXCEPT ![index] = [Proj(chain)[index] EXCEPT !.is_valid = FALSE]]
                    <5>a. lhs \in Seq(ChainEntry) OMITTED
                    <5>b. rhs \in Seq(ChainEntry) OMITTED
                    <5>1. Len(lhs) = Len(rhs) OMITTED
                    <5>2. \A i \in 1..Len(lhs): lhs[i] = rhs[i] OMITTED
                    <5> QED BY <5>a, <5>b, <5>1, <5>2, SeqEqual DEF h_chain, h_index
                <4>4. h_index' = h_index + 1 BY <3>1 DEF h_index
                <4>5. UNCHANGED h_state BY <3>1 DEF h_state
                <4> QED BY <4>1, <4>3, <4>4, <4>5
            <3> QED BY <3>1
        <2> QED
            BY <2>1, <2>2, <2>3 DEF Next, HSpec!Next
    \* next step (stutter)
    <1>3. UNCHANGED vars => UNCHANGED HSpec!vars
        BY DEF h_state, h_chain, h_index
    <1>4. QED
        BY PTL, <1>1, <1>2, <1>3 

================================================================================
\* Modification History
\* Last modified Sun Jul 21 22:54:30 JST 2019 by shinsa
\* Created Tue Jul 02 01:10:01 JST 2019 by shinsa
