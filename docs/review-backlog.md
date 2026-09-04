# ドキュメント後に検討する項目

この文書は、ドキュメント整備の途中で見つかった設計・命名・概念整理の課題を管理する。
読解中に気づいた違和感をすぐにソース改変へつなげず、一通り説明を書いたあとで影響範囲を見て対応する。

## 扱い方

- ドキュメント作業中に見つけた課題を、ここへ短く記録する。
- すぐ直さない理由と、後で見るべき影響範囲を書く。
- ソース変更が必要な場合は、読解ドキュメントが一巡してからまとめて検討する。
- 単なる表記ゆれではなく、読者の誤解や設計変更につながるものを優先する。

## 課題一覧

### Readingコード列の重複を保持する

状態: 要仕様変更

現在の `abstractWaitReadingCode` は、待ち牌を忘れてコードだけを取り出した後、`deduplicateAndSortBy id` で
同じコードの重複を除いている。そのため `2345678m` の3つの待ち牌 `2m`、`5m`、`8m` がいずれも
単騎と順子2つのコード338を持っていても、結果は `[338]` になり、3つのReadingがあるという多重度を失う。

望ましい基礎表現は、重複を保った正規順のコード多重集合である。この例なら `[338, 338, 338]` を返す。
多重集合からは明示的に重複を除いて現行のコード集合 `[338]` を導出できるが、集合から元の多重度は復元できない。
したがって、集合化が必要な集計だけを派生処理として分けるほうが一般性と表現力を保てる。

変更時に確認すること:

- `abstractWaitReadingCode` を重複保持へ変更するか、新しい多重集合APIを追加して現行APIを集合版として改名するか。
- 集合版には `...Set`、重複保持版には `...Multiset` または複数形 `...Codes` など、情報量が分かる名前を付けるか。
- `2345678m` の期待値を `[338, 338, 338]` とする最小テストを追加する。
- `MahjongComputations.FourTile` と `SevenTile` の `waitReadingCodes` グループキーを、多重集合と集合のどちらにするか。
- `irreducibleSevenTileAbstractWaitReadingClasses.length = 26` とレポートのグループ数・代表形がどう変わるか。
- 集合へ潰す用途では、多重集合からの射影であることと、その射影で失う情報を仕様として明示する。

実施時期は、`WaitReadingCode` のドキュメントが一巡した後、レポート層のドキュメントへ進む前がよい。
レポートの分類単位を説明した後で変更すると、読書順・期待値・生成済みレポートを二度直すことになるためである。

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
- `Reading` 系のモジュールを説明するときは、[domain-vocabulary.md](domain-vocabulary.md) の `Reading` 定義へ導く。
- 麻雀一般の「待ち読み」と違う意味であることを、初出時に明示する。

命名体系として後で確認すること:

- `AbstractWaitReading` の `Abstract` が、待ち牌を抽象化せず、部品の具体的な牌種列だけを忘れることを十分に表すか。
- `ConcreteWaitReading` と `AbstractWaitReading` の対比を、具体牌付き・部品種別のみという情報差が分かる名前にするべきか。
- `IrreducibleWaitReading` が牌姿全体の既約判定と誤解されないか。実際には完成面子を核成分列から分離した観測結果である。
- `WaitReadingComponentKind`、`ConcreteWaitReadingComponent` の `Component` が、`TileChunk` や説明語彙「完成部品」とどう対応するか。
- `Reading`、`TileChunk`、`Component`、`Core` を個別に改名せず、入力となる和了分割から情報を段階的に忘れる流れ全体で一貫した名前を選べるか。

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
- `AbstractWaitReading`、`ConcreteWaitReadingComponent` など、変換後の `Reading`・`Component` 系の名前と一体で見直すべきか。
- `DirectWaitReading`、`WaitCompletionFinder`、`WaitReadingCode` の読者向け語彙への影響。
- リネームする場合、既存の証明・レポート生成・テストへの影響。

### 完成部品列の標準順が型で保証されていない

状態: 保留

`TileChunk.canonicalize` は `List TileChunk` を標準順へ並べるが、返り値も通常の `List TileChunk` である。
そのため、任意の順番の列と標準順の列を型で区別できず、`WaitCompletion.winningChunks` が標準順であるかも
値だけからは分からない。

現在の `canonicalize_eq_of_perm` は、順列関係にある2入力が同じ標準順表現へ写ることを保証する。
一方で、「この値は標準順である」という不変条件をデータに持たせるものではない。

後で確認すること:

- 標準順であることを示す述語と仕様定理を公開するだけで十分か。
- `WaitCompletion.winningChunks` を、標準順の証拠を持つ構造体や専用型にすべきか。
- Finder以外から `WaitCompletion` を直接構築する既存コードやテストへの影響。
- `TileChunk` の改名と同時に、完成部品列を表す型の名前も設計すべきか。