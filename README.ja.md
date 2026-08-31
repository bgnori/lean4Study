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

主文書は Lean ソース内の module doc comment と doc comment です。README は入口と読み方を示し、詳細な仕様は Lean の定義と `example` に寄せます。これにより、説明とコードがずれたときに Lean の検査で気づける形にします。
