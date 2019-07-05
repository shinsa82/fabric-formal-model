------------------------------- MODULE Fabric -------------------------------
\* Hyperledger Fabric computation formal model
EXTENDS Sequences, FiniteSets, Naturals

\* Set of Clients, Peers, and Orderer(s)
CONSTANTS C, P, O, cid
ASSUME cid \in C

\* Set of argument(s), implicitly containing a function name
CONSTANTS TxId, Arg

VARIABLES msgs, ledger, state, txids
vars == <<msgs, ledger, state, txids>>

Transaction == [id: TxId, arg: Arg]


(* utilities and transitions *)
Send(m) == msgs' = msgs \union { m }

(* instances *)

Client == INSTANCE Client WITH Id <- cid

\*
\* Typical implementation of the spec
\* 
Init == msgs = {}
Next == \/ TRUE
Fairness == TRUE

Spec == Init /\ [][Next]_vars /\ Fairness

(*
 * Correctness properties (Safety, Liveness, ...)
 *)
CONSTANTS N \* Commit threshold
CONSTANTS Slot \* blockchain slot
CONSTANTS Key, Value, Version, Commit(_, _), State, RWSet
Peer(id) == INSTANCE Peer WITH Id <- id

(* 少なくとも定足数のピアに何かがコミットされている状態。なお Chosen は Paxos の用語 *)
Chosen(slot, tx) == \E peers \in SUBSET P:
    /\ Cardinality(peers) >= N
    /\ \A peer \in peers: Peer(peer)!Commit(slot, tx) \* なぜ Commit が Unknown に?

(* 何かが選択されている場合、選択されている tx は一意に決まる *)
(* almost trivial, all peers commit the very same block and transactions by protocol *) 
TxAgreement == \A slot \in Slot, tx1 , tx2 \in Transaction:
    Chosen(slot, tx1) /\ Chosen(slot, tx2) => tx1 = tx2

(*
以降の証明には Simulation = RWSet の決定、の特徴づけが必要。おそらく以下のような感じで大丈夫。TLA+ の記法に引き写す

Fabric ではStateの更新メカニズムが通常の replicated state machine のそれとは異なっている
consensus を取る前に、各ノードは TX の simulation を行う。この時点ではノードの state 更新されず、
simulation 結果は read-write set (RWSet とよぶ) の形で TX の endorsement として記録される

orderer を通過して各ノードで TX の commit (= TX の検証と state の更新) 処理を行う際に、TX endorsement の RWSet が検証され、
条件を満たすならば state の更新が行われる。その際には TX を直接実行するのではなく、RWSet に含まれる write set が現在の state に適用される

この方法が、commit 時に TX を直接実行する場合と等価になっていることを示すのが次の safety 命題である

なお、RWSet = ReadSet \X WriteSet = [Key -> Version] \X [Key -> Value]

(1: Read Set) 【間違ってる】 s1 と s2 が Read Set のドメインで一致するならば、f(s1) = f(s2)
(2: Write Set) s1 と f(s1) は、Write Set のドメインを除いては同一
バージョンが最新
バージョン番号も含めてdet.
*)
Simulate(s1, f, s2, rwset) == TRUE \* if f is applied at state s1, f(s1) = s2 and RWSet is rwset 
SefetyOfWriteSet == TRUE
SefetyOfReadSet == TRUE
SafetyOfSimulation == SefetyOfWriteSet /\ SefetyOfReadSet

ReadSetOK(s, rwset) == TRUE \* s satisfies rwset condition (= MVCC condition)  
ApplyTx(s1, f, s2) == TRUE \* f(s1) = s2
ApplyWriteSet(s1,rwset,s2) == TRUE \* committing WriteSet rwset at state s1 results in state s2

(*
状態 s1 で f(s1) を simulate すると s2 になり、そのときの RWSet は rwset とする。
任意の状態 s と、任意のtxと、そのsimulation結果 (rwset) について、 s が rwset の事前条件 (read set 条件) を満たしていれば、
s に tx を適用した結果の状態 s1 は、s に write set を適用した結果 s2 と一致する
*)
SafetyOfCommit == \A ss0, ss1, s, s1, s2 \in State, f, rwset \in RWSet:
    Simulate(ss0, f, ss1, rwset) /\ ReadSetOK(s, rwset) /\ ApplyTx(s, f, s1) /\ ApplyWriteSet(s,rwset,s2) => s1 = s2

(* あるスロットが選択状態なら、すべての正常なピアにおいて、その前のスロットすべてが選択状態*)

(* 一度コミットされたスロットは書き換わらない *)

(*
これにより、全てのスロットにおいて、そこで何かが選択されているならば、正常なピアにおいてその時点での状態は一致して
かつ、それはTXの本来の適用結果にひとしい?
 *)
StateAgreement == TRUE

(* これにより、本プロセス全体の振る舞いは単一の状態遷移系の simulation になる *)

Safety == StateAgreement
Liveness == TRUE \* to be written. but difficult to express

THEOREM Correctness == Spec => [](Safety /\ Liveness)

=============================================================================
\* Modification History
\* Last modified Tue May 14 13:49:49 JST 2019 by shinsa
\* Created Sun Mar 31 15:39:42 JST 2019 by shinsa
