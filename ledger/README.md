# Ledger 

Core part of the Fabric ledger spec.

## Status

- **作業中** v0.3: [MVCC_Ledger.tla](MVCC_Ledger.tla) のモデル化と refinement の証明
- v0.2: [Ledger.tla](Ledger.tla) で type 以外の invariant を証明
- v0.1: [Ledger.tla](Ledger.tla) で純粋な type invariant を証明

## Files

Read "モデリングの方針" for details. 上のものほど抽象度が高い。

- [Ledger.tla](Ledger.tla): Ledger のハイレベル仕様
- [MVCC_Ledger.tla](MVCC_Ledger.tla): Ledger の MVCC 仕様
- [MVCC_Consensus_Ledger.tla](MVCC_Consensus_Ledger.tla): Ledger の複数ノード MVCC 仕様

## インポート & 証明チェック方法 (TLA+ Toolbox での方法)

### プロジェクトのインポート

プロジェクト (`Specification`) のインポート機能がないようなのでこうする:

- 新規 `Specification` を作成する
-  [Ledger.tla](Ledger.tla) をルートファイルをして指定する
- `Module` を追加するメニューを選び、[MVCC_Ledger.tla](MVCC_Ledger.tla) と [MVCC_Consensus_Ledger.tla](MVCC_Consensus_Ledger.tla) を指定する

UI上、新規ファイルを作るような雰囲気で進むが、既存のファイルを指定すればそのようになるので問題ない。
また、TLAPS を使って証明するだけであれば、どれをルートファイルにしてもあまり関係ない

### 証明のチェック方法

Mac の場合、ファイルの先頭で `コマンド-g コマンド-g` をタイプすると証明が確認される。全部緑になればOK

- [Ledger.tla](Ledger.tla) では下部の `THEOREM` で type invariant とブロックチェーンに関する不変条件 `ChainInv` が証明されている

## インポート & 証明チェック方法 (Standalone tools での方法)

調査中

----

## 用語

- ピア (peer): データを保持・同期する計算ノード。次に述べるように台帳、さらにいうとその状態をもち、それらの同期をとることにより単一の state machine として外部に対して振る舞う。
  - 状態 (world state): state machine としての状態。各ピアの状態が同一であることが要求される。
  - 台帳 (ledger):
  - ブロックチェーン (blockchain): 台帳の同期をとるためのデータ構造
- リクエスト (request): クライアントから届いた生の形のサービスリクエスト。Ledger に対してす要求する操作 (operaton) の中身が書かれている。
- TX (transaction): リクエストが受け付けられて peer のキューに格納されるときの形式になったもの。

## モデリングの方針

3段階の refinement により証明する。

- 1段階目: ハイレベル仕様として、単一の peer で動作するモデルを考える。MVCC は適用しない。
リクエストが到達したら順番を確定させ、未処理 TX としてキューに格納する。処理時に操作を適用し、world state の状態を更新する。
- 2段階目: MVCCを適用。この時点では 1 peer のためあまり意味がないが後で使う。状態機械への適用をすぐに行うのではなくて、Orderer (未定義) に submit する前に peer で仮実行したものをリクエストに加えて TX として submit する。
- 3段階目: さらに複数の peer で仮実行結果を突き合わせることによって合意をとり、耐障害性などを担保する。
