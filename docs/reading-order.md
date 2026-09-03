# Lean未経験者向けの読む順番

この文書は、Leanを知らない読者が麻雀待ち分類の成果と正しさを追うための読み順を定める。
Leanの構文説明をすべてソースコメントに詰め込まず、必要な語彙を先に導入してから定義や定理を読む。

## 基本方針

文章は1次元にしか読めないため、コード上の依存関係と説明上の依存関係を分けて扱う。

- コード上の依存関係: Leanファイルがどの定義や定理を使っているか。
- 説明上の依存関係: 読者がその説明を理解するために先に知るべき概念や語彙。

読書体験では、説明上の依存関係を優先する。同じLean語彙の説明を各定理で繰り返さず、初出時に
[lean-vocabulary.md](lean-vocabulary.md) へ集約する。
麻雀待ち分類のプロジェクト語彙は [domain-vocabulary.md](domain-vocabulary.md) に集約する。

## 最初の入口

1. [lean-vocabulary.md](lean-vocabulary.md) の「最小語彙」を読む。
2. `Mahjong/Basic.lean` の牌種定義を読む。
3. `Tile.all` が34種類の牌種一覧であることを読む。
4. `Tile.mem_all` が、その一覧に抜けがないことを保証していることを読む。

この段階では、証明の細部をすべて追う必要はない。まずは「どの一覧に対して、何を保証しているか」を
理解する。

## その後の予定

次に読む実例は、待ち分類語彙の一覧性を示す `WellKnownWaitKind.exhaustive` である。ここでは
`Tile.mem_all` と同じく、列挙した分類名に抜けがないことを確認する読み方を使う。

読む前に知る語彙:

- `namespace`
- `theorem`
- `cases`
- `<;>`
- `simp`
- `[...]`
- `∈`

`Tile.mem_all` では牌種の一覧を確認した。`WellKnownWaitKind.exhaustive` では、待ち分類名の一覧を確認する。
これにより、後続の分類処理が参照する名前付き分類の表を、Leanが機械的に検査していることが分かる。

## 物理牌の枚数を読む

次の実例は、麻雀牌の山の枚数を示す `deck_cardinality` である。

読む前に知る語彙:

- `abbrev`
- `Finset`
- `.card`
- `theorem`
- `simp`
- `rfl`

ここでは、牌種 `Tile` と「同じ牌種が4枚ある」ことを表す `PhysicalTile` を区別する。
`deck_cardinality` は、物理牌全体の有限集合 `deck` の枚数が `deckSize` と一致すること、つまり
通常の麻雀牌の総数と同じになることを確認する。

## 牌を取り出す処理を読む

次のまとまりは、`Chunk.take` と、その基本仕様を示す `Chunk.take_fst`、`Chunk.take_snd_not_mem` である。

読む前に知る語彙:

- `structure`
- 部分型
- `×`
- `.1`
- `.2`
- `@[simp]`
- `theorem`
- `simp`
- `rfl`
- `∉`

ここでは、空でない物理牌集合 `Chunk` から、そこに含まれていると分かっている物理牌を1枚取り出す。
`Chunk.take` の返り値は `(取り出した牌, 残りの牌集合)` というペアである。

- `Chunk.take_fst`: 返り値の1番目が、指定した牌そのものであることを確認する。
- `Chunk.take_snd_not_mem`: 返り値の2番目には、取り出した牌がもう含まれないことを確認する。

この2つを合わせて、後で「取り出した牌」と「残りの牌」を分けて扱う処理の基本仕様になる。

## 牌種から物理牌を探す処理を読む

次のまとまりは、`takeTileFrom`、`takeTilesFrom`、`takeTiles` である。

読む前に知る語彙:

- `namespace`
- `noncomputable def`
- `Finset`
- `.1`
- `Option`
- `match`

`Chunk.take` は、取り出す物理牌がすでに分かっている場合の処理だった。
ここでは、牌種 `Tile` を指定し、それに対応する物理牌を有限集合の中から探して取り出す。

- `takeTileFrom`: 指定した牌種を持つ物理牌を1枚探して取り出す。
- `takeTilesFrom`: 牌種列を順に処理し、対応する物理牌列を取り出す。
- `takeTiles`: `Chunk` に対する入口として `takeTilesFrom` を呼ぶ。

このまとまりには、まだ仕様定理は付いていない。まずは「どの入力から何を探し、失敗時にどう表すか」を読む。

## 牌種列を持つ型を共通に扱う

次のまとまりは、`HasTilePattern` と `HasTilePattern.take` である。

読む前に知る語彙:

- `class`
- 型引数
- 型クラス引数
- `namespace`
- `noncomputable def`
- `Option`

`Chunk.takeTiles` は、牌種列 `List Tile` を直接渡す処理だった。
`HasTilePattern` は、具体的な型が何であっても「その値に対応する牌種列」を取り出せるなら、
同じ取り出し処理に渡せるようにする共通インターフェースである。

- `HasTilePattern`: 値から牌種列を取り出せる型であることを表す。
- `HasTilePattern.take`: `HasTilePattern.tiles` で牌種列を取り出し、`Chunk.takeTiles` に渡す。

ここから先のモジュールでは、待ちパターンや面子候補のような具体的な型が、この共通インターフェースに乗る。

## 牌の表示形式を読む

次のまとまりは、`Basic.lean` の `TileFormat` と `Tile.format` である。

読む前に知る語彙:

- `inductive`
- `def`
- `match`
- `example`
- `rfl`

`Tile.format` は、Lean上の牌種 `Tile` を読者が見慣れた文字列へ変換する。
`unicode` は麻雀牌のUnicode文字、`mpsz` は `1m`、`9p`、`5z` のような牌譜表記である。

この表示形式を先に読むと、次のターツや順子の例で、Lean上の牌種列が実際の牌姿としてどう見えるかを確認しやすくなる。

## 通常形のサイズと開始位置を読む

次のまとまりは、`Pattern.lean` 冒頭の手牌サイズ、`RyanmenStart`、`ShuntsuStart` である。

読む前に知る語彙:

- `abbrev`
- `def`
- `Fin`
- `Bool`

ここでは、通常形の手牌枚数や、順子・ターツの開始位置を表す補助定義を読む。
開始位置を `Fin` で表すことで、存在しない開始位置を型で除外している。
`RyanmenStart.lowerRank` と `upperRank` は両面ターツの2枚を、`ShuntsuStart.firstRank`、`middleRank`、`lastRank` は順子の3枚を計算する。

## 麻雀の小部品とデータ構造を読む

次のまとまりは、`Pattern.lean` の `Taatsu`、`Toitsu`、`Tanki`、`Shuntsu`、`MentsuCandidate` である。

読む前に知る語彙:

- `inductive`
- `namespace`
- `def`
- `instance`
- `HasTilePattern`
- `List Tile`
- `example`
- `rfl`

ここでは、麻雀上の概念とLean上のデータ構造の対応を先に押さえる。

- `Taatsu`: 両面・嵌張・辺張のような、完成まであと1枚の2枚組。
- `Toitsu`: 同じ牌種2枚からなる対子。
- `Tanki`: 単騎待ちの核になる1枚。
- `Shuntsu`: 同じスートで連続する3枚からなる順子。
- `MentsuCandidate`: 通常形で完成面子として扱う候補。順子または刻子。

それぞれの `tiles` は、その部品を構成する牌種列を返す。`HasTilePattern` のインスタンスにより、
これらの具体的な型は共通の物理牌取り出し処理に渡せる。
`Tile.format .mpsz` を使った `example` により、ターツ、対子、単騎、順子、刻子が実際の牌姿としてどう見えるかを確認する。
たとえば、両面 `23m`、嵌張 `35p`、辺張 `12s` と `89s`、対子 `55m`、単騎 `3p`、順子 `123s`、刻子 `777p` を確認する。

## 完成面子候補の列挙を読む

次の実例は、`MentsuCandidate.candidates` と `MentsuCandidate.mem_candidates` である。

読む前に知る語彙:

- `inductive`
- `namespace`
- `theorem`
- `cases`
- `rcases`
- `simp`
- `left`
- `refine`
- `?_`
- `exact`
- `∈`

`MentsuCandidate` は、通常形で完成面子として扱う候補を、順子または刻子として表す。
`MentsuCandidate.candidates` は、実行用に全順子候補と全刻子候補を並べたリストである。
`MentsuCandidate.mem_candidates` は、任意の完成面子候補がそのリストに含まれることを確認する。

この定理は、後で完成面子候補を列挙して探索するとき、列挙リストに取りこぼしがないことを支える。
刻子の場合には、すでに読んだ `Tile.mem_all` が使われる。

## 字牌を含む候補が順子ではないことを読む

次の実例は、`MentsuCandidate.IsShuntsu` と `MentsuCandidate.honor_not_in_shuntsu` である。

読む前に知る語彙:

- `Prop`
- `theorem`
- `∈`
- `¬`
- `cases`
- `simp`
- `at`

`MentsuCandidate.IsShuntsu` は、完成面子候補が順子であることを表す述語である。
`honor_not_in_shuntsu` は、字牌を含む完成面子候補が順子ではないことを確認する。

麻雀上、順子は同じスートの連続する数牌だけからなる。Lean上では、`Shuntsu.tiles` が数牌だけを返すため、
字牌が含まれるという仮定と両立しないことを `simp` で確認している。

## 雀頭と完成面子を同じ完成部品として読む

次のまとまりは、`TileChunk` と `TileChunk.tiles` である。

読む前に知る語彙:

- 直和 `⊕`
- `.inl`
- `.inr`
- `def`
- `instance`
- `example`

通常形の和了分割では、雀頭と完成面子をどちらも完成した部品として並べて扱う。
`TileChunk` は、雀頭 `Toitsu` または完成面子候補 `MentsuCandidate` のどちらかを持つ型である。

- `TileChunk.pair`: 雀頭を完成部品として作る。
- `TileChunk.shuntsu`: 順子を完成部品として作る。
- `TileChunk.koutsu`: 刻子を完成部品として作る。
- `TileChunk.tiles`: 完成部品を構成する牌種列を返す。

ここでも `Tile.format .mpsz` を使った `example` により、雀頭 `55m`、順子 `456p`、刻子 `777z` を確認する。

## 核成分列の抽出パターンを読む

次のまとまりは、`Wait.lean` の `WaitPattern` と `WaitPattern.tiles` である。

先に [domain-vocabulary.md](domain-vocabulary.md) の「待ち核」「待ち核集合」「可約と既約」を読む。

読む前に知る語彙:

- `inductive`
- `namespace`
- `List Tile`
- `++`
- `instance`
- `HasTilePattern`
- `example`
- `rfl`

`WaitPattern` は、完成面子を取り除いたあとに残る核成分列の抽出パターンを表す。
ここでは麻雀一般の「待ち読み」という語を避け、抽出に使うデータ構造として扱う。
実際に待ちであることの証明は `WaitCompletionFinder.IsWaitFor` が担当する。

- `tanki`: 単騎として扱う1枚。
- `toitsuRyanmen`: 対子と両面ターツからなる4枚の核成分列。
- `toitsuKanchan`: 対子と嵌張ターツからなる4枚の核成分列。
- `toitsuPenchan`: 対子と辺張ターツからなる4枚の核成分列。
- `shanpon`: 2つの対子からなる4枚の核成分列。

完成面子は `WaitPattern` に含めず、`HandExtraction.mentsuThen` による抽出過程として表す。
完成面子を取り除けるかどうかは、後続の `WaitReducibility` で別に扱う。
具体牌付きの核成分列は `IrreducibleWaitReading.core` に保持する。待ち牌と核成分列を組にして、
除去した完成面子の文脈を忘れて比較する形は `WaitCore` で表す。

`WaitPattern.tiles` は、それぞれの抽出パターンで必要になる牌種列を返す。
`Tile.format .mpsz` を使った `example` により、抽出パターンが実際の牌姿としてどう見えるかを確認する。

## 待ち分類と待ち核の曖昧性を読む

次のまとまりは、`WellKnownWaitKind`、`WaitAmbiguity`、`WaitClassification`、`WellKnownWaitKind.classification` である。

先に [domain-vocabulary.md](domain-vocabulary.md) の「待ち核の曖昧性」を読む。

読む前に知る語彙:

- `inductive`
- `structure`
- `def`
- `namespace`
- `theorem`
- `cases`
- `simp`

`WellKnownWaitKind` は、通常形聴牌に付けるよく知られた名前付き分類を表す。
これは待ちの数学的定義そのものではなく、待ち核集合に対して人間向けの分類名を与える層である。
`WaitAmbiguity` は、その名前付き分類が単一の待ち核に対応するか、複数の待ち核の共存に対応するかを表す。

`WaitClassification` は、分類名 `kind` と待ち核の曖昧性 `ambiguity` をまとめる。
`WellKnownWaitKind.classification` は、分類名だけからこのラベルを返す。
可約・既約は具体的な牌姿に依存するため、ここでは扱わず `WaitReducibility` で別に読む。

## 名前付き分類の仕様を読む

次のまとまりは、`Wait/Specification.lean` の `WaitProfileMentsu`、`WaitProfile`、`Classifies`、`expectedKind`、`expectedKind_iff` である。

先に [domain-vocabulary.md](domain-vocabulary.md) の「観測基本形」と「名前付き分類」を読む。

読む前に知る語彙:

- `inductive`
- `Prop`
- `abbrev`
- `def`
- `instance`
- `Decidable`
- `theorem`
- `↔`

`WaitProfile` は、待ち核集合から名前付き分類に必要な情報だけを取り出した観測基本形である。
単騎核については、分離された完成面子の文脈を `WaitProfileMentsu` に残す。

`Classifies` は、観測基本形の列がどの `WellKnownWaitKind` に属するかを宣言的に定める。
`expectedKind` は同じ規則を実行できる形にした参照実装で、`expectedKind_iff` が両者の一致を保証する。
`expectedKind_iff` の左から右は「参照実装が返した分類には仕様上の理由がある」という健全性、
右から左は「仕様上分類できるものは参照実装も返す」という完全性に対応する。

## 牌列から名前付き分類へ接続する解析器を読む

次のまとまりは、`Wait/Analysis.lean` の `observedWaitProfiles`、`classifyWaitProfiles_iff`、`classifyWait`、`classifyWait_iff` である。

先に [domain-vocabulary.md](domain-vocabulary.md) の「Reading」を読む。

読む前に知る語彙:

- `open`
- `let`
- `if`
- `filter`
- `flatMap`
- `theorem`
- `↔`
- `exact`

`observedWaitProfiles` は、牌列から待ち核集合を求め、名前付き分類に必要な観測基本形の列へ変換する。
`classifyWaitProfiles` は、その観測基本形列を `WaitSpecification.expectedKind` へ渡す。

`classifyWaitProfiles_iff` は、観測基本形上の解析器が `WaitSpecification.Classifies` と一致することを示す。
`classifyWait_iff` は、実際の牌列に対する分類結果が、牌列に対する名前付き分類仕様と一致することを示す。

## 可約性の計算と意味の一致を読む

次の実例は、`Wait/Analysis.lean` の `reducibility` と `reducibility_eq_reducible_iff` である。

先に [domain-vocabulary.md](domain-vocabulary.md) の「待ち核集合」と「可約と既約」を読む。

読む前に知る語彙:

- `def`
- `if`
- `theorem`
- `↔`
- `simp`

`reducibility` は、聴牌であることが確認済みの牌列について、待ち核集合を変えずに完成面子を除去できるかを調べる。
除去できれば `reducible`、できなければ `irreducible` を返す。

`reducibility_eq_reducible_iff` は、計算結果が `reducible` であることと、実際に待ち核集合を保つ面子除去が
可能であることが同値だと保証する。左から右は誤って可約と判定しないこと、右から左は可能な面子除去を
見落とさないことに対応する。

証明の `simp [reducibility]` は、`reducibility` の条件分岐を展開し、その判定条件が右辺の命題
`CanReduceMentsuPreservingWaitCores` そのものであることを確認する。
