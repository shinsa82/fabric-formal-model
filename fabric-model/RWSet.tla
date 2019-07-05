--------------------------------- MODULE RWSet ---------------------------------
(*
    Module that verifies safety of the MVCC algorithm

Fabric では state の更新メカニズムが通常の replicated state machine のそれとは異なっている。
State とは Fabric では (ほぼ) KVS のことであり、key から value への関数として表現される。
ここで、(key, value) なるペアをエントリとよぶことにする。
TX とは state への操作である。
通常の replicated state machine アルゴリズムとは異なり、Fabric ではノードたちが TX の順序に関するconsensus を取る前に、
    各ノードが TX の simulation を行う。
この時点では各ノードの state は更新されず、simulation の結果が read-write set (RWSet とよぶ) の形で TX の endorsement として記録される。

TX の実行順序が確定したのち、各ノードで TX の commit (= TX の検証と state の更新) 処理を行う。
そこで TX endorsement の RWSet が検証され、ある条件を満たすならば state の更新が行われる。
その際には TX を直接実行するのではなく、RWSet に含まれる write set が現在の state に適用される。
これは一般には MVCC (multi-version concurrency control) と呼ばれる。

ここで示したいのは、この方法が、commit 時に TX を直接実行する場合と等価になっていることを示すことである。

MVCC についてより詳しく説明する。

KVSを MVCC を使うために拡張し、"version" をエントリに含める。
つまり、KVS を key から (value, version) への関数に拡張する。 
これは各エントリが最後にいつ更新されたかを記録しておくものである。つまり、エントリへの書き込み時に version が更新される。
(注: ちょっと嘘をついている。実際には、ある TX の実行によって各エントリのバージョンは高々1回しか変わらない)
一般には version としては自然数が使われるが、ブロックチェーンの場合は "ブロック番号:TXインデックス" とすることも多い。

さらに、MVCCのために simulation 結果 (endorsement) も拡張する。
Read set には読んだエントリの key と、その (simulation 開始時における) version を記録する。
Write set はそのままである。つまり、書き込んだエントリの key と、書いた value  のペア (の集合) である。 

MVCC で TX (の endorsement) を commit する際行う検証は以下の通り:
Endorsement の read set のすべての要素 (k, v) について、現在の state におけるキー k のバージョンが v である場合に検証成功とする。

Fabric (およびその他の類似のシステム) が MVCC を使う理由については、私は、
    エントリの value を直接比較することは効率が悪いから
    であると理解している。

前記拡張した KVS のある2つの state を比較した場合において、version が異なれば value も異なるが逆は成り立たない。
よって MVCC を使うことにより、本来 commit できる TX が検証を通過できないことがあり得る。
つまり、MVCC の使用は速度性能と??? (注: なんて表現したらいいか、わからなかった) のトレードオフである。

以下、MVCC に関係する部分についてモデル化する。
まずは version を含まない KVS における TX 検証について上位仕様としてモデリングする。
*)

(*
    key, value, version に関する集合を定義。NULL 定数を定義
    NULL に関する型制約
    仮定には番号をつけておくと証明の際に便利、たぶん
*)
CONSTANTS Key, Version, Value, NULL
ASSUME A0 == NULL \notin (Value \union Key \union Version)

(*
State は KVS を表す。key から value への部分関数であるとする。
便宜上、全域関数に拡張しておく
*)
State == [Key -> (Value \union {NULL})]

(*
    f: Operation
    State への操作。単純化のため引数はないものとする。また失敗しないものとする。
    将来、決定的でない場合も考えるので relation とする
    Apply(s0, f, s1) の意味は f(s0) = s1 (see also Commit below)
    注: \A は forall, \E は exists の意味
*)
CONSTANTS Operation, Apply(_, _, _)
ASSUME A1 == \A s0, s1 \in State, f \in Operation: Apply(s0, f, s1) \in BOOLEAN

(*
f の決定性を表す命題。あとで使う
*)
Deterministic(f) == 
    \A s0, s11, s12 \in State: Apply(s0, f, s11) /\ Apply(s0, f, s12) => s11 = s12 

(*
    Write set を反映させる関数 Commit の宣言 (see also Apply)。これは全域である
    Write set の計算を非決定的なオペレーションとして定義 (ComputeWS)
    注: f[a] などは集合論的な意味での関数。一方 f(a) などはinstantiate可能な「オペレータ」を表す
*)
CONSTANT WriteSet, Commit(_, _)
ComputeWS[s1 \in State, s2 \in State] == CHOOSE w \in WriteSet: Commit(s1, w) = s2
ASSUME \A s1, s2 \in State: \E w \in WriteSet: Commit(s1, w) = s2

(*
    Read set は key の (空でない) 集合
*)
ReadSet == SUBSET Key \ {}

(*
Simulation の write set 計算部分 (SimulationWS) まず非決定的に定義 (TLA+でよくあるパターン)
補助定理
Operation f が決定的であるなら状態変化は決定的であるから、ComputeWS が関数であることにより SimulateWS の計算は決定的である。
*)
SimulateWS(f, s) == CHOOSE w \in WriteSet: (\E ss: Apply(s, f, ss) /\ ComputeWS[s, ss] = w)
LEMMA L1 == \A f \in Operation:
    Deterministic(f) => \A s0, s1 \in State:
        s0 = s1 => SimulateWS(f, s0) = SimulateWS(f, s1)
OMITTED

(*
これが証明できると、さらに強いことが言える。
State の全体が一致しなくても、あるキーの集合 r において値が一致していれば write set が一致するような r の存在が言える。
これは L1 より r = DOMAIN(State) = Key と取れることから示せる。
*)
SameOnKeys(s1, s2, r) == r \in ReadSet /\ \A k \in r: s1[k] = s2[k] 
RWSetSpec(f, s0, r, w) == \A s1 \in State: SameOnKeys(s0,s1,r) => 
    SimulateWS(f, s0) = SimulateWS(f, s1) /\  SimulateWS(f, s1) = w
LEMMA L2 == \A f \in Operation, s0 \in State: 
    Deterministic(f) => \E r, w: RWSetSpec(f, s0, r, w)
OMITTED

(* L2 より、Simulation 関数 (r に関して非決定的) を定義することができる (非決定的かもしれないが、少なくとも全域になる) *)
Simulate[f \in Operation, s \in State] == CHOOSE <<r, w>> \in Key \X WriteSet: RWSetSpec(f, s, r, w)

(* この関数を使って求めたい安全性が示せる *)
SafetyOfCommit == \A f \in Operation: Deterministic(f) =>
    \A s00 \in State: \A r \in ReadSet: \A w \in WriteSet: Simulate[f, s00] = <<r, w>> => 
        \A s10 \in State: SameOnKeys(s00, s10, r) => \A s11: Apply(f, s10, s11) => Commit(s10, w) = s11  
THEOREM SafetyOfCommit
OMITTED

(*
TODO: このあと version を入れたバージョン (つまり MVCC) の安全性を示す。
前述の naive なバージョンの refinement になるはず
*)

================================================================================
\* Modification History
\* Last modified Fri May 24 14:14:38 JST 2019 by shinsa
\* Created Tue May 14 13:52:12 JST 2019 by shinsa
