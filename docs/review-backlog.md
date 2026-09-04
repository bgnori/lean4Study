# ドキュメント後に検討する項目

この文書は、ドキュメント整備の途中で見つかった設計・命名・概念整理の課題を管理する。
読解中に気づいた違和感をすぐにソース改変へつなげず、一通り説明を書いたあとで影響範囲を見て対応する。

## 扱い方

- ドキュメント作業中に見つけた課題を、ここへ短く記録する。
- すぐ直さない理由と、後で見るべき影響範囲を書く。
- ソース変更が必要な場合は、読解ドキュメントが一巡してからまとめて検討する。
- 単なる表記ゆれではなく、読者の誤解や設計変更につながるものを優先する。

## 課題一覧

### 分解の操作履歴と外延的な正しさを分離する

状態: 要設計検証

`MentsuPartition` と `WinningPartition` は、実行器の再帰構造に近い帰納的な証拠を持つ。
各段階で、選んだ和了構成部品、その候補所属、`removeTiles` の具体的な戻り値、残りの分解証拠を保存する。
この形は `decomposeMentsu` と `winningPartitions` の健全性・完全性を直接証明しやすい一方、利用側が
必要とする外延的な性質を得るたび、操作履歴を順列の意味へ変換し直す必要がある。

ドキュメント整備で、次の小定理と証明パターンが連続して現れた。

- `MentsuPartition.of_perm`: 除去履歴を別の入力順へ移す。
- `MentsuPartition.tiles_perm`: 各除去履歴から牌全体の保存則を復元する。
- `MentsuPartition.all_mentsu`: 各構築段階の候補所属を列全体の条件として取り出す。
- `MentsuPartition.components_length`: 帰納段階と `fuel` の対応を列長として取り出す。
- `WinningPartition.of_perm`: 雀頭除去後の残り長を揃えて、面子分解証拠を移す。
- `WinningPartition.tiles_perm`: 面子側の保存則へ雀頭除去の保存則を再び連結する。

証明の粒度が細かく見える主因は、必要な数学的性質が細かいというより、順序依存の操作履歴と
順序非依存の仕様が同じ証拠表現に重なっていることかもしれない。

既存定理から、少なくとも `MentsuPartition` は次の外延的な条件と同値になると予想できる。

```lean
components.length = fuel ∧
	(∀ component ∈ components, component ∈ mentsuComponentCandidates) ∧
	(components.flatMap WinningComponent.tiles).Perm tiles
```

左から右は `components_length`、`all_mentsu`、`tiles_perm` で示せる。右から左は、まず
`mentsuPartition_flatMap` で部品順に連結した牌列の分解証拠を作り、`of_perm` で入力牌列へ移し、
列長の等式で `fuel` を揃えれば示せるはずである。この同値定理は、仮説を安価に検証できる最初の対象になる。

後で確認すること:

- 上の外延的特徴づけ定理を追加し、証明が既存補助定理の短い合成で閉じるか。
- `DirectWaitReading` の利用側を、帰納的証拠の `cases` ではなく外延的仕様経由で簡潔にできるか。
- `WinningPartition` も「先頭が雀頭候補」「末尾がすべて面子候補」「全和了構成部品牌が入力牌列の順列」
	という外延的条件で特徴づけられるか。
- `remaining.length / mentsuTileCount` は実行器の再帰回数としてだけ計算し、宣言的仕様の基本表現から
	外せるか。特に `WinningPartition.of_perm` の `sameLength` と添字の書き換えが不要になるか。
- 帰納的関係は実行器との対応証明専用に残し、公開仕様には外延的述語または構造体を使う二層構成が
	読みやすいか。置き換える場合も、計算可能な列挙器と健全性・完全性定理は維持する。
- 外延的仕様を新しい構造体にするなら、候補所属、列長、牌の順列を個別フィールドにする価値があるか、
	単一の `Prop` と特徴づけ定理で十分か。

### `amb`型の探索抽象で候補生成と成功条件を表す

状態: 検討

可約性判定は、完成面子を試しに1つ取り除き、残った牌列が聴牌であり、かつ待ち核集合を保つ枝が
存在するかを調べている。考え方としては、Schemeの`amb`における「候補を非決定的に選び、
条件を満たさない枝を失敗させ、成功する枝を残す」探索に近い。

現行コードでも、この非決定性はすでに `List` で表現されている。

- `mentsuComponentCandidates`: 取り除く完成面子を選ぶ。
- `filterMap (removeTiles tiles)`: 実際に取り除けない候補を失敗枝として捨てる。
- `mentsuReductions`: 成功した残り牌列をすべて列挙する。
- `List.any`: 聴牌と待ち核集合保存の条件を満たす枝が存在するか判定する。

この流れを、Leanの `List` を使った非決定的計算、`do`記法、または小さな探索APIとして明示すれば、
「候補生成」「失敗による枝刈り」「成功条件」の対応が読みやすくなり、同種の探索処理を簡潔に書ける可能性がある。
一方、Scheme風の新しい概念や記法を導入するだけでは、Lean上の証明や実行効率を改善せず、既存の
`filterMap`、`flatMap`、`any`より理解すべき抽象を増やす可能性もある。

後で確認すること:

- まず `mentsuReductions` と `canReduceMentsuPreservingWaitCores` を `List` の `do`記法で試作し、
	現行コードより候補選択と枝刈りが明瞭になるか。
- Boolの存在判定だけでなく、成功した除去面子、残り牌列、待ち核一致の証拠を返す探索にも再利用できるか。
- 実行用の有限探索と、健全性・完全性を述べる命題側の存在量化を対応付けやすくなるか。
- 探索順、重複候補、全解列挙、最初の解、解の存在判定を、同じ基礎表現から必要に応じて導出できるか。
- `WaitCompletionFinder`、`Hand`、`DirectWaitReading` にある他の `flatMap` / `filterMap` 型探索にも
	共通化する価値があるか。
- `WaitAmbiguity` は待ち分類上の曖昧性であり、非決定的探索の意味ではないため、名前や説明を混同しないこと。
- 抽象化する場合も、現在のリスト実装と同等の計算可能性を保ち、探索エンジンを新たに自作する必要がないか。

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

`WinningComponent` と Reading 側の `Component` の関係は整理済み。
前者は待ち牌を除く前の和了構成部品、後者は除去後または保持後の観測成分であり、
[domain-vocabulary.md](domain-vocabulary.md) に変換関係を明記した。

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

### `TileChunk` と周辺の `Chunk` 系識別子を改名する

状態: 対応済み

旧 `TileChunk := Toitsu ⊕ MentsuCandidate` は、通常形の和了分割に現れる
「雀頭または完成面子候補」を表していた。一方、`Basic.lean` の `Chunk` は物理牌の有限集合であり、
同じ `Chunk` 語幹が異なる概念を指していた。

対応では `WinningComponent` を採用した。`CompletedComponent` は待ち牌除去後の観測成分との
「完成・不完全」の対比を強くしすぎ、`StandardComponent` は標準形以外との比較を想定させ、
`MeldOrPair` は実装表現を列挙するだけで和了分割との関係を示さないため採用しなかった。

同時に次を改名した。

- `WaitCompletion.winningChunks` → `winningComponents`
- `pairChunkCandidates` / `mentsuChunkCandidates` → `pairComponentCandidates` / `mentsuComponentCandidates`
- `WinningShape.chunk` / `chunks` → `component` / `components`
- 和了構成部品を指す補助変数・定理名の `chunk(s)` → `component(s)`

物理牌集合 `Chunk` とその引数名 `chunk` は別概念として維持した。コード検索で残る `Chunk` は、
この物理牌集合を指すものに限定した。

`AbstractWaitReading` は維持した。これは `WinningComponent` の別名ではなく、待ち牌を除いた観測結果から
具体牌列だけを忘れた型である。`ConcreteWaitReadingComponent` と `WaitReadingComponentKind` も同様に
Reading内部の観測成分を指すため、`WinningComponent` と役割を分けて読める。

日本語説明は「完成部品」から「和了構成部品」へ変更し、コードの `WinningComponent` と対応させた。
これにより、完成面子、待ち牌除去後の観測成分、物理牌集合 `Chunk` との区別を明示する。

### 和了構成部品列の標準順が型で保証されていない

状態: 保留

`WinningComponent.canonicalize` は `List WinningComponent` を標準順へ並べるが、返り値も通常の `List WinningComponent` である。
そのため、任意の順番の列と標準順の列を型で区別できず、`WaitCompletion.winningComponents` が標準順であるかも
値だけからは分からない。

現在の `canonicalize_eq_of_perm` は、順列関係にある2入力が同じ標準順表現へ写ることを保証する。
一方で、「この値は標準順である」という不変条件をデータに持たせるものではない。

後で確認すること:

- 標準順であることを示す述語と仕様定理を公開するだけで十分か。
- `WaitCompletion.winningComponents` を、標準順の証拠を持つ構造体や専用型にすべきか。
- Finder以外から `WaitCompletion` を直接構築する既存コードやテストへの影響。
- 和了構成部品列を表す専用型を設計すべきか。