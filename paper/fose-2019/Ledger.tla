-------------------------------- MODULE Ledger --------------------------------
EXTENDS Sequences, Integers, TLAPS, Datatype

VARIABLES state,    \* current state of the ledger state machine.
          chain,    \* blockchain, a list of received transactions. 
          index     \* unprocessed TX index at the blockchain.
vars == <<state, chain, index>>

ChainEntry == [tx: TX, is_valid: BOOLEAN \union {NULL}] 
Chain == Seq(ChainEntry)

Init ==
    /\ state = InitState    \* state is at the initial state, and 
    /\ index = 1
    /\ chain = <<>>         \* empty transaction queue.

SubmitTX(tx) ==
    /\ chain' = Append(chain, [tx |-> tx, is_valid |-> NULL])
    /\ UNCHANGED <<state, index>> 

ProcessTX_OK ==
    LET
        f == chain[index].tx.f
    IN
        \* /\ Len(chain) >= index
        /\ index \in DOMAIN chain
        /\ chain' = [chain EXCEPT ![index].is_valid = TRUE]  \* update validity flag
        /\ index' = index + 1   \* increment the index.
        /\ state' \in f[state]  \* perform non-deterministic state transition by f.
        
ProcessTX_ERR ==
    LET
        f == chain[index].tx.f
    IN
        \* /\ Len(chain) >= index
        /\ index \in DOMAIN chain
        /\ chain' = [chain EXCEPT ![index].is_valid = FALSE]  \* see above.
        /\ index' = index + 1  \* see above.
        /\ UNCHANGED state     \* state does not change due to invalid TX.

Next == (\E tx \in TX: SubmitTX(tx)) \/ ProcessTX_OK \/ ProcessTX_ERR

Spec == Init /\ [][Next]_vars
================================================================================
