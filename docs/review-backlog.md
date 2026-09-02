# ドキュメント後に検討する項目

この文書は、ドキュメント整備の途中で見つかった設計・命名・概念整理の課題を管理する。
読解中に気づいた違和感をすぐにソース改変へつなげず、一通り説明を書いたあとで影響範囲を見て対応する。

## 扱い方

- ドキュメント作業中に見つけた課題を、ここへ短く記録する。
- すぐ直さない理由と、後で見るべき影響範囲を書く。
- ソース変更が必要な場合は、読解ドキュメントが一巡してからまとめて検討する。
- 単なる表記ゆれではなく、読者の誤解や設計変更につながるものを優先する。

## 課題一覧

### Tanki実装変更後の可約・既約レポート差分を確認する

状態: 保留

Tanki関係の実装変更後に `fourTileReport` を再生成したところ、4枚形の集計で可約・既約の数が変わった。

- 旧: reducible 1674、irreducible 2082
- 新: reducible 1647、irreducible 2109

例として、`1223m` や `1233m` は旧レポートでは `reducible` だったが、新レポートでは `irreducible` になっている。
新しい実装では、単騎を完成面子付きの4枚終端としてではなく、完成面子を分離した後の核成分列として扱うため、
この差分は意図に沿っている可能性が高い。

後で確認すること:

- 旧実装で、既約であるべき牌姿が誤って可約に分類されていたか。
- `canReduceMentsuPreservingWaitCores` が、待ち核集合にもとづく可約性として期待どおりか。
- レポート内の `waitReadingCodes` グループ `[21, 26]`、`[26, 33]` が新たに既約側へ出ている理由。
- 検証が必要なら、`1223m` と `1233m` を最小例として仕様・テストに落とすか。

### `Reading` と「読み」という日本語説明の衝突を避ける

状態: 対応中

`DirectWaitReading` や `WaitReadingCode` には、プロジェクト内の技術語として `Reading` が出てくる。
一方で、麻雀一般にも「待ち読み」という言葉があり、これは相手の待ちを推測する意味で使われやすい。

`WaitPattern` の説明で「待ちをどう読むか」と書くと、プロジェクト内の `Reading` とも麻雀一般語彙とも衝突し、
読者が混乱する可能性が高い。

対応方針:

- `WaitPattern` の説明では、原則として「読み」ではなく「抽出パターン」または「終端抽出」を使う。
- `HasNobetanReading` の名前に残る `Reading` が、プロジェクト内技術語や麻雀一般語彙と衝突しないか確認する。
- `Reading` 系のモジュールを説明するときに、プロジェクト内の `Reading` が何を意味するかを改めて定義する。
- 麻雀一般の「待ち読み」と違う意味であることを、初出時に明示する。

### `WellKnownWaitKind` が基本分類と通称・複合分類を同じ層に置いている

状態: 保留

`WellKnownWaitKind` は現在、`tanki`、`toitsuRyanmen`、`toitsuKanchan`、`toitsuPenchan`、`shanpon` に加えて、
`nobetan` や `kuttsuki...` 系を同じ列挙に含めている。

麻雀ルール上の基本的な待ち分類としては `shanpon` まででよく、`nobetan` 以降は通称・複合的な読みとして
別の層に分けたほうが、読者にとって自然な可能性がある。

後で確認すること:

- `WellKnownWaitKind` を基本分類と通称・複合分類に分けるべきか。
- `WaitClassification`、`WellKnownWaitKind.classification`、`WellKnownWaitKind.ambiguity` の役割をどう切るか。
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