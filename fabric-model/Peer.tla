-------------------------------- MODULE Peer --------------------------------
EXTENDS Sequences

CONSTANTS Id, \* Id of the peer, given by the Fabric.tla
          Key, Value, Version, \* Set of keys, values, and its version 
          Arg, \* arguments, implicitly includes a function name as the first argument
          Transaction,  \* Transactions, given by the Fabric.tla
          Slot \* index of slots where txs are committed. Actually it should be #block_num:#tx_index. To be fixed.
          \* Commit(_,_) \* commit action 

Commit(slot,tx) == TRUE

VARIABLES  msgs, \* Message buffer, given by the Fabric.tla
           ledger \* Ledger of the peer

LOCAL vars == <<msgs, ledger>> 

(* typedefs *)

LOCAL Send(m) == msgs' = msgs \union { m }

State == [Key -> (Value \X Version)] \* State DB
Chain == Seq(Transaction) \* Blockchain
RWSet == [read: SUBSET (Key \X Version) , write: SUBSET (Key \X Value)]
SC == [(State \X Arg) -> RWSet] \* At this point, we assume it's deterministic
Ledger == [chain: Chain, state: State, sc: SC] 

\*ASSUME \A stateBefore, stateAfter, rwset:
\*    Commit(stateBefore, rwset, stateAfter) \in BOOLEAN

(* actions *)

Simulate(tx) ==
  LET
    arg == tx.arg
    rwset == ledger.sc[ledger.state, arg] 
  IN Send([type |-> "endorsement", from |-> Id, rwset |-> rwset])

(******************************************************************************)
(* Spec template                                                           *)
(******************************************************************************) 

Init == msgs = {} /\ ledger = [chain: <<>>, state: {}, sc: {}]
Next == \E m \in msgs, tx \in Transaction: 
    m.type = "invoke" /\ m.tx = tx /\ Simulate(tx)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Wed Apr 17 16:12:10 JST 2019 by shinsa
\* Created Thu Apr 04 15:06:48 JST 2019 by shinsa
