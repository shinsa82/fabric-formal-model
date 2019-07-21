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
Operation == TotalFunc(State, SUBSET State)
TX == [f: Operation] \* a transaction. note that "f" is just a label

================================================================================
\* Modification History
\* Last modified Fri Jul 19 17:58:47 JST 2019 by shinsa
\* Created Fri Jul 19 17:56:23 JST 2019 by shinsa
