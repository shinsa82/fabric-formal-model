------------------------------- MODULE Datatype -------------------------------
(******************************************************************************)
(* Common datatypes                                                           *)
(******************************************************************************)

(******************************************************************************)
(* Constants                                                                  *)
(******************************************************************************)
CONSTANTS State, InitState \* a set of states, and 
ASSUME InitStateAxiom == InitState \in State \* the designated initial state.
NULL == CHOOSE x : x \notin BOOLEAN 

TotalFunc(S1, S2) == [ S1 -> S2 \ {{}} ]\* a set of total function from S1 to S2 
Operation == TotalFunc(State, SUBSET State) \* an operation, which changes the state.
TX == [f: Operation] \* a transaction record. "f" is a label of the record

================================================================================
\* Modification History
\* Last modified Wed Jul 24 19:51:08 JST 2019 by shinsa
\* Created Fri Jul 19 17:56:23 JST 2019 by shinsa
