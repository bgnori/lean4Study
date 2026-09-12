# lean4Study

Lean 4 と mathlib の学習用リポジトリです。中心的な題材として、麻雀の牌、ターツ、面子、通常形の待ちの意味論、待ち核を Lean で形式化し、計算例や theorem によって確認します。

[English version](README.md)

## 目的

- 具体的な題材を Lean の型としてモデル化しながら Lean 4 を学ぶ。
- `example ... := by native_decide` などを使い、例を実行可能な仕様として残す。
- 実装、仕様、証明、ドキュメントをできるだけ同じ場所で育てる。

## 構成

```text
.
├── Main.lean              # Lean/mathlib の小さな練習
├── Haskell.lean           # List や関数定義の練習メモ
├── NaturalLimited.lean    # 有限型、Finset、濃度の学習メモ
├── Lean4Project.lean      # ライブラリ全体の入口
├── Mahjong.lean           # Mahjong モジュールの入口
├── Mahjong/               # 麻雀の形式化
│   ├── Basic.lean
│   ├── Pattern.lean
│   ├── Hand.lean
│   ├── WaitCompletion.lean
│   ├── WaitCompletionFinder.lean
│   ├── WaitDecompositionCode.lean
│   ├── DirectWaitGeneration.lean
│   ├── Tenpai.lean
│   └── README.md
├── MahjongTests/         # 計算量の大きい回帰テスト
├── MahjongComputations/  # 全列挙と集計レポート
├── docs/                 # 読書順、Lean語彙、プロジェクト語彙
└── reports/              # 生成済みレポート
```

## ビルド

全体を確認する場合:

```bash
lake build
```

麻雀部分だけを確認する場合:

```bash
lake build Mahjong
```

計算量の大きい回帰テストと全列挙を明示的に確認する場合:

```bash
lake build MahjongTests
lake build MahjongComputations
```

4枚形・7枚形のレポートを生成する場合:

```bash
lake build fourTileReport
lake build sevenTileReport
```

出力先はそれぞれ `reports/four-tile-direct-report.txt` と `reports/seven-tile-report.txt` です。

### 大規模計算用Codespaces

`.devcontainer/devcontainer.json`は32 CPU、64 GB RAM、64 GB storageを最低要件として宣言している。
Dockerの`--cpus`・`--memory`制限は設定せず、選択したCodespaces machineの資源をコンテナから
利用できるようにしている。Codespace作成時に32-core machineを選び、作成後は次を確認する。

```bash
nproc
cat /sys/fs/cgroup/memory.max
df -h /workspaces
```

devcontainer設定を変更した既存Codespaceでは、**Codespaces: Rebuild Container**を実行する。
長時間計算は`tmux`内で起動し、GitHubのCodespaces設定でidle timeoutを最大の240分へ変更する。
terminal出力もidle timeoutをリセットするため、数時間無出力になる計算には定期的な進捗表示を持たせる。

CPU数をそのまま分類worker数にしない。外部bucket生成は多くのcoreを使えるが、分類はworkerごとに
bucket内HashMapを保持するためメモリ使用量も増える。13枚形は生成worker、分類worker、bucket数を
分けて指定できる。32-core Codespaceでの初回候補は次の通り。

```bash
lake exe thirteen-tile-report-gen --generation-workers=32 --classification-workers=8 --buckets=256
```

生成完了後は`.lake/build/thirteen-tile-buckets/generation.done`が作られる。分類中に停止した場合、
同じ設定で再実行すると既存bucketを再利用して分類から再開する。cacheの永続化やbucketごとの
checkpointは行わない。生成からやり直す場合は`.lake/build/thirteen-tile-buckets`を削除する。

単一ファイルを直接確認する場合:

```bash
lake env lean Mahjong/WaitCompletionFinder.lean
```

## ドキュメント

読者向け:

- [docs/introduction.md](docs/introduction.md): Lean4と証明付きプログラムが今回の用途で何を支えるか。
- [docs/reading-order.md](docs/reading-order.md): Lean未経験者向けの読む順番。
- [docs/lean-vocabulary.md](docs/lean-vocabulary.md): `namespace`、`theorem`、`cases`、`simp` などの初出説明。
- [docs/domain-vocabulary.md](docs/domain-vocabulary.md): 待ち核、可約、既約など、このプロジェクト内の説明語彙。

作成・保守側の方針:

- [docs/documentation-policy.md](docs/documentation-policy.md): 読者向け文書、語彙ページ、保守用文書の役割分担。
- [docs/proof-comment-policy.md](docs/proof-comment-policy.md): 定義・定理コメントに書くことと、語彙ページへ逃がすことの切り分け。
- [docs/review-backlog.md](docs/review-backlog.md): ドキュメント整備後に検討する設計・命名課題。

麻雀モジュール単位の概要は [Mahjong/README.md](Mahjong/README.md) を参照してください。
