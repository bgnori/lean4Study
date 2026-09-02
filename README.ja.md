# lean4Study

Lean 4 と mathlib の学習用リポジトリです。中心的な題材として、麻雀の待ち分類を Lean で形式化しています。牌、ターツ、面子、通常形の待ちの意味論、名前付き待ち分類を定義し、4枚ケースは `example` や theorem によって確認します。

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
├── Mahjong/               # 麻雀の待ち分類の形式化
│   ├── Basic.lean
│   ├── Pattern.lean
│   ├── Wait.lean
│   ├── Wait/Specification.lean
│   ├── Wait/Analysis.lean
│   ├── Hand.lean
│   ├── WaitCompletion.lean
│   ├── WaitCompletionFinder.lean
│   ├── WaitReadingCode.lean
│   ├── Tenpai.lean
│   └── README.md
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

単一ファイルを直接確認する場合:

```bash
lake env lean Mahjong/WaitCompletionFinder.lean
```

## ドキュメント方針

ソースコメントは局所説明、`docs/` はLean未経験者向けに線形化された読書体験、語彙ページは重複回避の辞書として使います。

- [docs/reading-order.md](docs/reading-order.md): Lean未経験者向けの読む順番。
- [docs/lean-vocabulary.md](docs/lean-vocabulary.md): `namespace`、`theorem`、`cases`、`simp` などの初出説明。
- [docs/proof-comment-policy.md](docs/proof-comment-policy.md): 定義・定理コメントに書くことと、語彙ページへ逃がすことの切り分け。
- [docs/review-backlog.md](docs/review-backlog.md): ドキュメント整備後に検討する設計・命名課題。

Lean ソース内の module doc comment と doc comment は、定義や定理が麻雀待ち分類の中で何を意味するかに集中します。一般的なLean構文やタクティクの説明は `docs/lean-vocabulary.md` に集約します。
