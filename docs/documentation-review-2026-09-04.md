# ドキュメンテーションレビュー報告 2026-09-04

## 対象

- ルート README: [README.md](../README.md), [README.ja.md](../README.ja.md)
- Mahjong モジュール概要: [Mahjong/README.md](../Mahjong/README.md)
- 計算モジュール概要: [MahjongComputations/README.md](../MahjongComputations/README.md)
- 読書導線と語彙: [reading-order.md](reading-order.md), [lean-vocabulary.md](lean-vocabulary.md), [domain-vocabulary.md](domain-vocabulary.md), [proof-comment-policy.md](proof-comment-policy.md)
- 設計・命名の保留事項: [review-backlog.md](review-backlog.md)
- 関連する主要ソースコメント: [Mahjong/WaitDecompositionCode.lean](../Mahjong/WaitDecompositionCode.lean), [Mahjong/DirectWaitGeneration.lean](../Mahjong/DirectWaitGeneration.lean)

## 総評

現在のドキュメントは、Lean 未経験者が麻雀待ち分類の実装と証明を読むための導線としてよく整理されている。特に、Lean 構文を [lean-vocabulary.md](lean-vocabulary.md) へ逃がし、プロジェクト固有語彙を [domain-vocabulary.md](domain-vocabulary.md) へ分離する方針は、ソースコメントの重複を抑えるうえで有効である。

一方で、既存実装の変化に対して追随しきれていない小さな古い記述と、長大化した読書順ドキュメントの保守負荷が見える。重大な概念崩れは見つからなかったが、レポート出力名の不一致は利用者が古い成果物を参照する可能性があるため、優先して直す価値がある。

## 所見

### 1. `MahjongComputations/README.md` の 4 枚形レポート出力先が古い

重要度: 高

[MahjongComputations/README.md](../MahjongComputations/README.md) は `lake build fourTileReport` の出力先を `reports/four-tile-report.txt` と説明している。しかし [lakefile.lean](../lakefile.lean) の `fourTileReport` target と [MahjongComputations/FourTileReport.lean](../MahjongComputations/FourTileReport.lean) の既定出力先は `reports/four-tile-direct-report.txt` である。ルート README の英日版も `reports/four-tile-direct-report.txt` と書いており、計算モジュール README だけがずれている。

影響:

- 読者が `lake build fourTileReport` 後に古い `reports/four-tile-report.txt` を確認してしまう。
- 既存の `reports/four-tile-report.txt` が残っている場合、現在の生成結果ではなく過去のレポートを正しい成果物と誤認する。
- ルート README とサブディレクトリ README の説明が食い違い、レポート層の信頼性が落ちる。

推奨対応:

- [MahjongComputations/README.md](../MahjongComputations/README.md) の出力先を `reports/four-tile-direct-report.txt` に更新する。
- `reports/four-tile-report.txt` が現在も意味を持つ成果物なのか、旧生成物なのかを決める。旧生成物なら README またはレポート一覧から参照しない。

### 2. `WaitPattern` の説明が `HandExtraction.mentsuThen` に寄りすぎている

重要度: 中

後続の概念整理で、実行経路から孤立していた `WaitPattern` と `HandExtraction` は削除された。
待ち核の抽出は `WaitDecompositionCode` の `WaitCoreExtraction` と `waitCores` に一本化された。

### 3. `reading-order.md` が包括的すぎて、更新単位が大きい

重要度: 中

[docs/reading-order.md](reading-order.md) は、基礎定義から直接生成器と有限添字仕様までを一続きの読書体験として説明している。局所説明は丁寧だが、文書全体が長く、モジュール追加や仕様変更のたびにどの節を更新すべきかが見えにくい。

影響:

- 小さな実装変更でも、該当箇所を探すコストが高い。
- `review-backlog.md` にあるような仕様変更、特に `waitDecompositionCodes` の重複保持化が入ると、複数箇所の説明と例が同時に古くなりやすい。
- 読者にとって、今どこまでが基礎、どこからが発展・仕様確認なのかが見えにくい。

推奨対応:

- 冒頭に短い目次と「基礎」「Finder」「分類」「待ち分解コード」「直接生成」の区切りを追加する。
- 各大区分の末尾に、次に読むファイルとそこで確認する代表定理を 2、3 個だけ置く。
- 将来的には文書分割も検討できるが、まずは目次と区切りだけで更新コストを下げられる。

### 4. 英語 README と日本語 docs の役割分担が少し曖昧

重要度: 低

ルートには英日 README があり、深い docs は日本語中心である。一方、[Mahjong/README.md](../Mahjong/README.md) と [MahjongComputations/README.md](../MahjongComputations/README.md) は英語で、[docs/reading-order.md](reading-order.md) や [docs/domain-vocabulary.md](domain-vocabulary.md) への日本語導線とは少し温度差がある。

影響:

- 日本語版 README から入った読者が、モジュール単位の README で英語へ切り替わる。
- 英語 README から入った読者には、日本語 docs が主たる読解ガイドであることが分かりにくい。

推奨対応:

- `Mahjong/README.md` に「詳しい読書順は日本語 docs にある」ことを明示する。
- 必要なら `Mahjong/README.ja.md` を追加するか、既存 `Mahjong/README.md` を短い英日併記にする。
- 英語版の完全整備を急がないなら、英語 README 側で Japanese-first documentation であることを明示するだけでも十分である。

### 5. `review-backlog.md` は有用だが、状態語の粒度を揃える余地がある

重要度: 低

[docs/review-backlog.md](review-backlog.md) は、ドキュメント作業中に見つかった設計・命名課題をソース改変から切り離して管理できている。特に待ち分解コードの多重度のような概念設計の未決事項と、`WinningComponent` 改名時の判断記録が具体例付きで残っている点は有用である。

一方で、状態が `要設計検証`、`検討`、`要仕様変更`、`保留`、`対応中` などに分かれており、優先度や次の作業が一目では比較しにくい。

推奨対応:

- 状態語を `未着手`, `調査中`, `実装前に要判断`, `仕様変更候補`, `保留` 程度に整理する。
- 各項目に「次の最小確認」を 1 行で置く。例: `1223m` と `1233m` の期待値をテストに落とす、など。

## 良い点

- Lean 一般語彙とプロジェクト語彙の分離が明確で、ソースコメントが構文説明で膨らみにくい。
- 観測結果を待ち分解、直接生成の証人を待ち導出として区別し、麻雀一般の「待ち読み」との衝突を避けている。
- `waitDecompositionCodes` が重複を失うことを隠さず、現行仕様と変更候補を [domain-vocabulary.md](domain-vocabulary.md) と [review-backlog.md](review-backlog.md) の両方で追跡している。
- 仕様定理を「健全性」「完全性」として読む導線が一貫している。
- 生成レポート、計算量の大きいテスト、通常ビルドを分ける説明は、開発時の期待値を合わせるのに役立っている。

## 先に直す順番

1. [MahjongComputations/README.md](../MahjongComputations/README.md) の 4 枚形レポート出力先を修正する。
2. 待ち核の説明を `WaitDecompositionCode` の実行経路へ揃える。
3. [docs/reading-order.md](reading-order.md) の冒頭に目次と大区分を追加する。
4. `Mahjong/README.md` に日本語 docs への導線、または日本語読者向けの短い説明を加える。
5. [docs/review-backlog.md](review-backlog.md) の状態語と「次の最小確認」を揃える。

## 確認したこと

- `lakefile.lean` の `fourTileReport` target は `reports/four-tile-direct-report.txt` を書く。
- `MahjongComputations/FourTileReport.lean` の既定出力先も `reports/four-tile-direct-report.txt` である。
- ルート README の英日版は、4 枚形と 7 枚形の出力先を現行 target と一致して説明している。
- Markdown 内の相対リンクは、確認した範囲では既存ファイルを指している。
- `waitDecompositionCodes` の重複排除については、実装コメント、語彙ページ、読書順、review backlog の説明が概ね一致している。