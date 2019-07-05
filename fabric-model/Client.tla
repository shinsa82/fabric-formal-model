------------------------------- MODULE Client -------------------------------
(******************************************************************************)
(* Clients send transaction proposal to Peers, collect endorsement from them, *)
(* send them to the Orderer. They also query Peer's state to one of the Peers.*)
(******************************************************************************)

EXTENDS FiniteSets

CONSTANTS Transaction, \* Transactions, given by the Fabric.tla
          Id \* Id of the client, given by the Fabric.tla

VARIABLES msgs
vars == <<msgs>>

(*
typedefs
*)

(*
utilities and transitions *) LOCAL Send(m) == msgs' = msgs \union { m }

Invoke(tx) ==
    /\ tx \in Transaction
    /\ Send([type |-> "invoke", from |-> Id, tx |-> tx]) 

Query(tx) ==
    /\ tx \in Transaction
    /\ Send([type |-> "query", from |-> Id, tx |-> tx]) 


(*
 * spec template
 *) 
Init == msgs = {}
Next == \E tx \in Transaction: Invoke(tx) \/ Query(tx)
FAIRNESS == WF_vars(Next)
Spec == Init /\ [][Next]_vars /\ FAIRNESS

(*
 * Correctness properties (Safety, Liveness, ...)
 *)

SampleLiveness == <>(/\ (\E m \in msgs: m.type="invoke")
                     /\ (\E m \in msgs: m.type="query")) 
SampleLiveness2 == <>(/\ (\A m \in msgs: m.type="invoke"))
SampleInvariant == [](\A m \in msgs: m.type="invoke")
=============================================================================
\* Modification History
\* Last modified Fri Apr 05 03:06:26 JST 2019 by shinsa
\* Created Thu Apr 04 15:46:41 JST 2019 by shinsa
