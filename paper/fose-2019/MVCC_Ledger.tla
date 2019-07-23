------------------------------ MODULE MVCC_Ledger ------------------------------
...
Endorsement == RWSet 
\* each entry of blockchain now has a RWSet.
ChainEntry == [tx: TX, endorsement: Endorsement, is_valid: BOOLEAN \union {NULL}] 
...
SubmitTX(tx) ==
    LET
        end == endorsement(tx)
    IN
        /\ chain' = Append(chain, [tx |-> tx, endorsement |-> end, is_valid |-> NULL])
        /\ UNCHANGED <<state, index>> 
...
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
...
h_state == state
h_chain == Proj(chain)
h_index == index
...
HSpec == 
    INSTANCE Ledger WITH state <- h_state, chain <- h_chain, index <- h_index

THEOREM Refinement == Spec => HSpec!Spec
...

================================================================================
