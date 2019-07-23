-------------------------------- MODULE Ledger --------------------------------
...
Spec == Init /\ [][Next]_vars

---
\* Invariant (safety) on the blockchain
ChainInv ==
    \* chain = (processed part) + (unprocessed part) 
    /\ \A i \in 1 .. index-1: chain[i].is_valid \in BOOLEAN
    /\ \A i \in {i \in Nat: index <= i} \cap DOMAIN chain: chain[i].is_valid = NULL

Inv == TypeInv /\ ChainInv

(* Invariant (safety) on the high-level Ledger *) 
THEOREM LedgerInv == Spec => []Inv
PROOF
    <1>1 Init => Inv
        BY InitStateAxiom DEF Init, Inv, TypeInv, ChainInv, Chain
    <1>2 Inv /\ [Next]_vars => Inv'
        <2>1 SUFFICES ASSUME TypeInv, ChainInv, [Next]_vars PROVE Inv' BY DEF Inv
        <2>2 CASE Next
            <3> USE DEF Inv, Next
...
    <1> QED BY PTL, <1>1, <1>2 DEF Spec
  
================================================================================
