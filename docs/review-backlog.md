# ドキュメント後に検討する項目

この文書は、ドキュメント整備の途中で見つかった設計・命名・概念整理の課題を管理する。
読解中に気づいた違和感をすぐにソース改変へつなげず、一通り説明を書いたあとで影響範囲を見て対応する。

## 扱い方

- ドキュメント作業中に見つけた課題を、ここへ短く記録する。
- すぐ直さない理由と、後で見るべき影響範囲を書く。
- ソース変更が必要な場合は、読解ドキュメントが一巡してからまとめて検討する。
- 単なる表記ゆれではなく、読者の誤解や設計変更につながるものを優先する。

## 課題一覧

### `WaitKind` がルール上の分類と通称を混ぜている

状態: 保留

`WaitKind` は現在、`tanki`、`toitsuRyanmen`、`toitsuKanchan`、`toitsuPenchan`、`shanpon` に加えて、
`nobetan` や `kuttsuki...` 系を同じ列挙に含めている。

麻雀ルール上の基本的な待ち分類としては `shanpon` まででよく、`nobetan` 以降は通称・複合的な読みとして
別の層に分けたほうが、読者にとって自然な可能性がある。

後で確認すること:

- `WaitKind` を基本分類と通称分類に分けるべきか。
- `WaitClassification`、`WaitKind.classification`、`WaitKind.ambiguity` の役割をどう切るか。
- `Mahjong.Wait.Specification` と `Mahjong.Wait.Analysis` の定理名・返り値への影響。
- 既存レポートや `WaitReadingCode` の表示語彙への影響。

### `TileChunk` という名前が概念を誤解させる可能性がある

状態: 保留

`TileChunk := Toitsu ⊕ MentsuCandidate` は、通常形の和了分割に現れる「雀頭または完成面子候補」を表す。
一方で、`Basic.lean` には物理牌集合を表す `Chunk` があり、`TileChunk` という名前だけでは
「牌の集合」なのか「和了分割の完成部品」なのかが分かりにくい。

また、`TileChunk` は雀頭も含むため、`Mentsu` に近い名前へ寄せると誤解を招く。
意味としては「完成済み部品」に近い。

候補名:

- `CompletedComponent`
- `WinningComponent`
- `StandardComponent`
- `MeldOrPair`

現時点の第一候補は `CompletedComponent`。雀頭と完成面子候補の両方を含められ、物理牌集合 `Chunk` とも区別しやすい。

後で確認すること:

- `TileChunk` の参照範囲。
- `WaitCompletion.winningChunks` など、周辺の `Chunk` 系の名前も同時に見直すべきか。
- `DirectWaitReading`、`WaitCompletionFinder`、`WaitReadingCode` の読者向け語彙への影響。
- リネームする場合、既存の証明・レポート生成・テストへの影響。