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

先に [domain-vocabulary.md](domain-vocabulary.md) の「和了分割の完成部品」を読む。

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

## 完成部品の整列キーが情報を失わないことを読む

次の実例は、`WaitCompletion.lean` の `TileChunk.orderKey` と `TileChunk.orderKey_injective` である。

読む前に知る語彙:

- `Nat`
- `Function.Injective`
- `native_decide`

和了分割では、同じ完成部品が異なる順番で並ぶことがある。後続処理で順番の違いをなくすため、
`TileChunk.orderKey` は雀頭、順子、刻子を自然数へ写し、その数値順で並べられるようにする。

3種類の完成部品には互いに重ならない数値範囲を使う。雀頭の範囲の後に全順子、その後に全刻子を置き、
各範囲内では牌種、スート、順子の開始位置を使って区別する。ソース中の `example` は、雀頭 `55m`、
順子 `456p`、刻子 `111z` がそれぞれ異なる範囲のキー `4`、`44`、`82` を持つことを確認する。

`orderKey_injective` は、キーが等しい2つの完成部品は元から等しいことを保証する。
したがって、整列のために数値キーを使っても、異なる完成部品が同じものとして扱われることはない。
証明は、有限個の `TileChunk` の全組合せを `native_decide` で計算して確認する。

## 完成部品列を標準順で表す

次の実例は、`WaitCompletion.lean` の `TileChunk.canonicalize` と `TileChunk.canonicalize_eq_of_perm` である。

先に [domain-vocabulary.md](domain-vocabulary.md) の「完成部品列の標準順表現」を読む。

読む前に知る語彙:

- `List.Perm`
- `mergeSort`
- `apply`
- `intro`
- `simpa` と `using`
- `omega`
- `.trans` と `.symm`
- `exact`

同じ和了分割でも、探索過程によって雀頭や面子が異なる順番で列に入ることがある。
`canonicalize` は、前節で読んだ `orderKey` の昇順に完成部品を並べ、入力時の順番の違いをなくす。
整列は部品を追加・削除しないため、各部品とその個数はそのまま残る。

ここで標準化される対象は `TileChunk` 単体ではなく、和了分割を表す `List TileChunk` である。
また、同一視するのはリスト上の順番だけであり、異なる分割や牌姿を同じものにする処理ではない。
返り値は通常の `List TileChunk` なので、標準順であること自体は型から判別できない。

ソース中の `example` は、雀頭 `55m` と順子 `456p` の順番を入れ替えた2つの列が、
標準順へ変換した後には同じ列になることを計算で確認する。

`canonicalize_eq_of_perm` は、この具体例を任意の完成部品列へ一般化する。
仮定 `first.Perm second` は、2つの列が同じ要素を同じ個数だけ持ち、順番だけが異なり得ることを表す。
証明は、両方の結果がキー順に整列済みであることと、整列前後で要素と個数が変わらないことを使う。
さらに `orderKey_injective` がキーの衝突を除外するため、2つの整列結果は要素ごとに一致する。

これにより、後続のReading生成は、和了分割の部品が偶然どの順番で発見されたかに影響されず、
含まれる完成部品とその個数に基づいて比較できる。

## 牌種列から指定した枚数だけ取り除く

次の実例は、`WaitCompletionFinder.lean` の `removeTiles` と `removeTiles_append_left` である。

読む前に知る語彙:

- `List Tile`
- `Option`
- `List.erase`
- `++`
- `induction`
- `nil` と `cons`
- `rfl`
- `simp`

`removeTiles available wanted` は、利用可能な牌種列 `available` から、必要な牌種列 `wanted` を
1枚ずつ取り除く。すべて取り除ければ残りを `some` で返し、途中で必要な牌がなければ `none` を返す。
ここで扱うのは集合ではなくリストなので、同じ牌種の出現回数が区別される。

ソース中の `example` では、利用可能な牌列を `55m 1p`、除去対象を `5m` とする。
`removeTiles` は `5m` を1枚だけ除くため、もう1枚の `5m` と `1p` が残る。

`removeTiles_append_left` は、利用可能な牌列を `wanted ++ remaining` として作れば、`wanted` の除去が
必ず成功して `remaining` をそのまま返すことを保証する。この定理が直接扱うのは、この連結順で作った入力である。
入力順一般に対する成功条件は、直前の `exists_removeTiles_eq_some_iff_perm` が順列を使って別に特徴づけている。

証明は `wanted` の長さに沿った帰納法で読む。空なら何も除かない。先頭牌がある場合はその1枚を除き、
残りの牌列について帰納法の仮定を使う。この保証により、後続の分割探索は、候補の牌を元の牌列へ
連結して作った場合に、その候補を確実に取り戻せる。

## 雀頭候補の列挙に過不足がないことを読む

次の実例は、`WaitCompletionFinder.lean` の `pairChunkCandidates`、
`pair_mem_pairChunkCandidates`、`pair_of_mem_pairChunkCandidates` である。

読む前に知る語彙:

- `map`
- `∈`
- `∃`
- `rcases`
- `obtain`
- `List.mem_map`
- `simp`
- `exact`
- `rfl`

和了分割の探索では、34種類の牌種それぞれについて、その牌種2枚を雀頭とする候補を試す。
`pairChunkCandidates` は `Tile.all` の各牌種を `TileChunk.pair` で雀頭の完成部品へ変換したリストである。
ソース中の `example` は、赤牌の雀頭もこの候補列に含まれることを計算で確認する。

候補列挙には、必要な候補を取りこぼさない完全性と、余計な種類を混ぜない健全性の両方が必要になる。

- `pair_mem_pairChunkCandidates`: 任意の雀頭が候補列に含まれるため、雀頭を取りこぼさない。
- `pair_of_mem_pairChunkCandidates`: 候補列の各要素は何らかの雀頭なので、順子や刻子が混ざらない。

完全性の証明は、雀頭を構成する牌種が `Tile.all` に含まれるという、先に読んだ `Tile.mem_all` を使う。
健全性の証明は、候補が `map` 元のどの牌種から作られたかを取り出し、その牌種の対子を存在例として返す。
この2定理を合わせると、後続の和了分割探索が調べる雀頭候補は、全雀頭とちょうど一致する。

## 完成面子候補を完成部品として列挙する

次の実例は、`WaitCompletionFinder.lean` の `mentsuChunkCandidates`、
`mentsu_mem_mentsuChunkCandidates`、`mentsu_of_mem_mentsuChunkCandidates` である。

先に、`MentsuCandidate.candidates` と `MentsuCandidate.mem_candidates` の節を読む。

読む前に知る語彙:

- `map`
- `.inr`
- `List.mem_map`
- `.mp` と `.mpr`
- `_root_`
- `∈`
- `∃`
- `obtain`
- `exact`
- `rfl`

先の節では、すべての順子・刻子が `MentsuCandidate.candidates` に含まれることを確認した。
`mentsuChunkCandidates` は、その各候補を直和 `TileChunk` の完成面子側 `.inr` に包む。
順子や刻子の内容を変えるのではなく、雀頭と同じ完成部品列へ入れられる形に持ち上げる処理である。

雀頭候補と同様に、2つの定理が列挙の両方向を保証する。

- `mentsu_mem_mentsuChunkCandidates`: 任意の順子・刻子を包んだ値が候補列に含まれる。
- `mentsu_of_mem_mentsuChunkCandidates`: 候補列の各要素は何らかの順子・刻子を包んだ値である。

完全性は、既存の `MentsuCandidate.mem_candidates` を `List.mem_map.mpr` で写像後の所属へ移す。
健全性は、`List.mem_map.mp` で写像元の完成面子候補を取り出す。
ソース中の `example` は、字牌の刻子 `777z` も完成部品候補に含まれることを確認する。

この2定理により、後続の分割探索が完成面子として試す候補は、先に列挙した全順子・刻子とちょうど一致し、
雀頭候補とは直和の左右で区別される。

## 牌種列を指定個数の完成面子へ分解する

次の実例は、`WaitCompletionFinder.lean` の `decomposeMentsu` である。

読む前に知る語彙:

- `fuel`
- `fuel + 1`
- `List (List TileChunk)`
- `List.flatten`
- `map`
- `match`
- `[]` と `::`

`decomposeMentsu fuel tiles` は、牌種列全体をちょうど `fuel` 個の順子・刻子へ分解する方法を列挙する。
`fuel` は「最大で何個まで試すか」ではなく、求める完成面子の個数である。

返り値の外側のリストは、異なる分解方法の列である。各内側の `List TileChunk` が、
1つの分解を構成する完成面子列になる。したがって、次の2つは意味が異なる。

- `[]`: 条件を満たす分解方法が1つもない。
- `[[]]`: 完成面子を0個使う空の分解が1通りある。

`fuel = 0` の場合、入力牌列も空なら `[[]]`、牌が1枚でも残っていれば `[]` を返す。
ソース中の2つの `example` は、この基底ケースの違いを `rfl` で確認する。

`fuel + 1` の場合は、前節の `mentsuChunkCandidates` から最初の完成面子を1つずつ試す。
その牌を `removeTiles` で除けた枝だけについて、残りの牌をちょうど `fuel` 個へ再帰的に分解する。
各候補から得た分解列を `List.flatten` で1つにつなぐため、可能な分解を1つに決めず、すべて返す。

この段階では実行可能な列挙処理を読む。直後の `MentsuPartition` が同じ分解を宣言的に表し、
`mem_decomposeMentsu_iff` が列挙結果との一致を保証する。

## 完成面子への分解を証拠として表す

次の実例は、`WaitCompletionFinder.lean` の `MentsuPartition` である。

読む前に知る語彙:

- `Prop`
- 添字付きinductive family
- inductive型のconstructor
- 暗黙の引数
- `.done` と `.next`
- `apply`
- `exact`

`decomposeMentsu` は可能な分解をすべてリストとして計算した。`MentsuPartition fuel tiles chunks` は、
特定の完成面子列 `chunks` が、牌種列 `tiles` をちょうど `fuel` 個へ分解した結果として正しいことを表す。
3つの引数は次の意味を持つ。

- `fuel`: 分解に使う完成面子の個数
- `tiles`: 分解前の牌種列
- `chunks`: 分解結果の完成面子列

これは分解結果を新たに探索する関数ではなく、3者の関係が正しいことを表す命題である。
証拠は2つのconstructorで組み立てる。

- `done`: 空の牌種列を0個の完成面子へ分解した基底ケース
- `next`: 完成面子を1つ選び、残りの牌種列に対する分解証拠の前へ追加する再帰ケース

`next`を使うには、選んだ値が`mentsuChunkCandidates`に含まれること、入力からその面子の牌を除けること、
除去後の牌種列も残りの面子へ分解できることの3つを示す必要がある。この条件により、雀頭を完成面子として
混ぜたり、入力にない牌を使った分解証拠を作ったりできない。

ソース中の`777z`の例は、`next`で字牌刻子を1つ選び、候補所属、3枚の除去、残りの空列に対する`done`を
順に与える。これにより、`777z`がちょうど1個の完成面子へ分解できることをLeanが確認する。

次の`mem_decomposeMentsu_iff`では、実行器の返すリストに`chunks`が含まれることと、
この`MentsuPartition`の証拠が存在することが同値だと示す。

## 面子分解の実行器と宣言的仕様の一致を読む

次の実例は、`WaitCompletionFinder.lean` の `mem_decomposeMentsu_iff` である。

読む前に知る語彙:

- `↔`
- 健全性と完全性
- `induction ... generalizing`
- `constructor`
- `split`
- `List.mem_flatten`
- `List.mem_map`
- `.mp` と `.mpr`
- `subst`
- `rw`
- `▸`
- `rename_i`

定理の左辺 `chunks ∈ decomposeMentsu fuel tiles` は、実行器が列挙した分解の中に`chunks`があることを表す。
右辺 `MentsuPartition fuel tiles chunks` は、同じ`chunks`が正しい分解であるという宣言的な証拠を表す。
定理はこの2つが同値であり、実行と仕様の間にずれがないことを保証する。

左から右は健全性に対応する。列挙結果に含まれる分解について、`flatten`から最初の候補の枝を、
`map`から残りの分解を取り出す。候補所属、`removeTiles`の成功、帰納法で得た残りの証拠を
`MentsuPartition.next`へ渡すため、実行器が不正な分解を返さないことが分かる。

右から左は完全性に対応する。`MentsuPartition.next`から最初の完成面子、除去の成功、残りの分解証拠を取り出す。
帰納法の仮定で残りの分解が再帰呼び出しの結果に含まれることを示し、その分解が最初の候補に対応する
`map`と`flatten`の枝に存在することを組み立てる。したがって、仕様上正しい分解を実行器が取りこぼさない。

証明は`fuel`に対する帰納法で進むが、再帰呼び出しでは入力牌列と完成面子列が変化する。
そのため`generalizing tiles chunks`で両者を固定せず、各帰納段階で任意の値に対して使える仮定にする。
`fuel = 0`では、両側とも入力牌列と完成面子列が空の場合だけ成立することを確認する。

ソース末尾の`777z`の例は、前節で作った`MentsuPartition`の証拠を同値定理の`.mpr`方向へ渡し、
実際に`decomposeMentsu 1`の列挙結果へ含まれることを確認する。

## 面子分解が入力順に依存しないことを読む

次の実例は、`WaitCompletionFinder.lean` の `MentsuPartition.of_perm` である。

読む前に知る語彙:

- `List.Perm`
- `induction ... generalizing`
- `List.Perm.nil_eq`
- `obtain`
- `.trans` と `.symm`
- `subst`

定理は `MentsuPartition fuel tiles chunks` と `tiles.Perm other` から、
`MentsuPartition fuel other chunks` を作る。完成面子列 `chunks` とその個数 `fuel` は変えず、
入力牌列だけを同じ牌種を同じ枚数持つ `other` へ置き換える。

これは、分解証拠の意味が入力リストの偶然の並び順に依存しないことを保証する。ただし、牌種やその枚数を
変えてよいわけではない。`List.Perm` が許すのは順番の変更だけで、重複数は保存される。

証明は分解証拠に対する帰納法で進むが、帰納段階では並べ替え後の入力から先頭面子を除いた新しい残り牌列へ
移る。そのため `generalizing other` により、特定の `other` に固定しない帰納法の仮定を用意する。

- `done`: 元の入力 `tiles` は空である。空列と順列関係にある `other` も `List.Perm.nil_eq` により空なので、`subst other` の後に `.done` を返す。
- `next`: 元の入力から先頭面子を除いた結果 `remaining` と、並べ替え後の入力から同じ面子を除いた結果 `output` を対応させる。

`remove` を `exists_removeTiles_eq_some_iff_perm` へ渡すと、`mentsu.tiles ++ remaining` と元の入力 `tiles` の
順列 `removedPerm` が得られる。これを仮定の `tiles.Perm other` と `.trans` でつなぐと、同じ先頭面子を
`other` からも除けることが分かる。同値定理の逆向きは、実際の除去結果 `output` と、
`output.Perm remaining` も同時に返す。

帰納法の仮定が必要とする向きは `remaining` から新しい残り `output` なので、`outputPerm.symm` で順列を反転する。
これにより末尾の分解証拠を `output` へ移し、新しい除去結果と合わせて `.next` を作り直せる。

ソース中の例は、整列した `123m` の順子分解を直接構築し、入力だけを `312m` へ並べ替えた分解証拠を
`of_perm` で得る。完成面子は同じ `123m` の順子のままである。

## 面子分解が入力牌を保存することを読む

次の実例は、`WaitCompletionFinder.lean` の `MentsuPartition.tiles_perm` である。

読む前に知る語彙:

- `List.flatMap`
- `List.Perm`
- `induction`
- `List.Perm.append_left`
- `.trans`

`chunks.flatMap TileChunk.tiles` は、分解結果の各完成面子を3枚の牌種列へ戻し、それらを順番に連結する。
定理の結論 `(chunks.flatMap TileChunk.tiles).Perm tiles` は、この復元した牌列と元の入力牌列 `tiles` が、
同じ牌種を同じ枚数だけ含むことを表す。

ここで等号ではなく `List.Perm` を使うのは、分解結果では牌が面子ごとにまとまる一方、入力牌列では
異なる面子の牌が混ざった順番でもよいからである。順番の差は許すが重複数は保存するため、この定理から
分解処理が牌を失わず、余分な牌を加えず、同じ牌種の枚数も変えないことが分かる。

証明は `MentsuPartition` の証拠に対する帰納法で進む。

- `done`: 入力牌列と完成面子列はどちらも空なので、空列自身の順列を返す。
- `next`: 先頭面子を除いた計算結果と、末尾の分解証拠を組み合わせる。

`next` に保存された `remove` を `exists_removeTiles_eq_some_iff_perm` の左から右へ使うと、
「先頭面子の牌 `mentsu.tiles` と除去後の `remaining` を連結した列」が、その段階の入力 `tiles` の
順列であるという `removedPerm` を得る。

一方、帰納法の仮定 `inductionHypothesis` は、末尾の完成面子を牌へ戻した列が `remaining` の順列であると保証する。
`List.Perm.append_left` で両方の先頭へ `mentsu.tiles` を加えれば、全完成面子の牌列と
`mentsu.tiles ++ remaining` の順列になる。最後に `.trans removedPerm` で入力牌列まで関係をつなぐ。

ソース中の例は、赤牌刻子 `777z` と萬子順子 `123m` の完成部品列を使う。入力側では両面子の牌を
交互に並べているため列としては等しくないが、`tiles_perm` により同じ牌を同じ枚数だけ持つことを取り出せる。

## 面子分解の全要素が完成面子候補であることを読む

次の実例は、`WaitCompletionFinder.lean` の `MentsuPartition.all_mentsu` である。

読む前に知る語彙:

- `∀`
- `induction`
- `intro`
- `List.mem_cons`
- `rcases`
- `rfl | restMember`
- `exact`

定理の結論 `∀ chunk ∈ chunks, chunk ∈ mentsuChunkCandidates` は、分解結果`chunks`から
任意の要素`chunk`を1つ選ぶと、それが完成面子候補列に含まれることを表す。

`MentsuPartition.next`は、完成面子を追加するたびに、その値が`mentsuChunkCandidates`に含まれるという
`candidate`証拠を要求していた。`all_mentsu`は、この局所的な条件が完成した分解列の全要素について
保存されていることを取り出す定理である。

証明は`MentsuPartition`の証拠に対する帰納法で進む。

- `done`: 分解結果が空なので、調べる要素は存在しない。
- `next`: 要素が先頭なら、その段階の`candidate`が直接使える。末尾の要素なら、残りの分解に対する帰納法の仮定を使う。

`rcases List.mem_cons.mp member with rfl | restMember`は、調べている要素が先頭そのものの場合と、
末尾に含まれる場合へ分ける。先頭の場合は`rfl`によってその要素を現在の完成面子と同一視する。

この定理だけでは候補の内部構造までは展開しない。前に読んだ`mentsu_of_mem_mentsuChunkCandidates`と合わせると、
各要素が何らかの順子または刻子を`.inr`に包んだ値であり、雀頭は混ざらないことが分かる。
ソース中の例は、`777z`の1面子分解から、その刻子が完成面子候補に含まれることを取り出す。

## 面子分解を型付き候補列として復元する

次の実例は、`WaitCompletionFinder.lean` の `MentsuPartition.exists_candidates` である。

読む前に知る語彙:

- `∃`
- `List.map`
- 直和の `.inr`
- `induction`
- `obtain`
- `rfl`
- `⟨...⟩`

`TileChunk` は雀頭または完成面子を持てる型だが、面子分解の `chunks` に雀頭は現れない。
定理はこの事実を、次のように列全体の形として表す。

```lean
∃ candidates : List MentsuCandidate,
  chunks = candidates.map fun candidate => (Sum.inr candidate : TileChunk)
```

右辺は、順子または刻子だけを持つ `candidates` の各要素を、`TileChunk` の完成面子側である
`.inr` へ入れた列である。この列が `chunks` と等しいため、雀頭が混ざらないだけでなく、
元の要素の順番と重複を保ったまま `MentsuCandidate` の列へ戻せる。

証明は `MentsuPartition` の証拠に対する帰納法で進む。

- `done`: 分解結果は空なので、復元する候補列にも `[]` を選ぶ。
- `next`: 先頭の `candidate` 証拠へ `mentsu_of_mem_mentsuChunkCandidates` を使い、具体的な順子または刻子 `first` を取り出す。残りの分解から帰納法で得た `rest` の先頭へ `first` を追加する。

2回の `obtain` にある `rfl` は、取り出した値に合わせて先頭の完成部品と末尾の列をその場で
書き換える。その結果、最後に選ぶ復元列 `first :: rest` を `map` した値と元の列は定義上同じになり、
`rfl` で証明できる。

ソース中の例は、`777z` の1面子分解に対応する `MentsuCandidate` 列が存在し、それを `.inr` へ
写した列が元の赤牌刻子の列に一致することを、この定理から直接取り出す。

## 面子分解の個数保証を読む

次の実例は、`WaitCompletionFinder.lean` の `MentsuPartition.chunks_length` である。

読む前に知る語彙:

- `List.length`
- `induction`
- `rfl`
- `simp [inductionHypothesis]`

定理の結論 `chunks.length = fuel` は、分解結果に含まれる完成面子の個数が、分解証拠の
`fuel` と一致することを表す。ここから、`fuel` は探索を途中で打ち切るための上限ではなく、
その分解が実際に含む完成面子の個数だと確認できる。

この一致は `MentsuPartition` の2つの構築規則に埋め込まれている。

- `done`: `chunks` は空列で `fuel` は `0` なので、両辺は定義上同じである。
- `next`: 先頭に完成面子を1つ追加すると `chunks.length` は1増え、構築規則も `fuel + 1` を結論にする。

証明は分解証拠に対する帰納法で、この2規則をそのまま辿る。`done` は `rfl` で閉じる。
`next` では、残りの列について得た `inductionHypothesis` を `simp` に渡すと、両辺から共通の
1個分を除いた等式へ単純化できる。

ソース中の `777z` の例では、1個の赤牌刻子からなる分解証拠にこの定理を適用し、
結果列の長さが `1` であることを確認する。`all_mentsu` が各要素の種類を保証したのに対し、
`chunks_length` は列全体の要素数を保証する。

## 完成面子列から分解証拠を組み立てる

次の実例は、`WaitCompletionFinder.lean` の `mentsuPartition_flatMap` である。

読む前に知る語彙:

- `List.flatMap`
- `∀`
- `induction`
- `have`
- `simp`
- inductive型のconstructor `.done` と `.next`

これまでの `all_mentsu`、`exists_candidates`、`chunks_length` は、すでにある `MentsuPartition` の
証拠から性質を取り出す定理だった。`mentsuPartition_flatMap` は逆向きに、すべての要素が
`mentsuChunkCandidates` に含まれる部品列 `chunks` から分解証拠を組み立てる。

`chunks.flatMap TileChunk.tiles` は、各完成面子を構成する3枚の牌種列を、部品の順番どおりに
すべて連結する。定理の結論は、この牌列をちょうど `chunks.length` 個へ分解すると、元の
`chunks` 自身が正しい分解になることを述べる。

証明は `chunks` に対する帰納法で進む。

- `nil`: 部品も牌もないため、空の分解を表す `.done` を使う。
- `cons`: `allMentsu` から先頭 `first` の候補所属と、末尾 `rest` の全要素の候補所属を取り出す。帰納法の仮定へ後者を渡して末尾の分解証拠 `tail` を作る。

先頭部品の牌列を平坦化後の入力から除くと、末尾を平坦化した牌列が残る。この計算は前に読んだ
`removeTiles_append_left` が保証する。先頭の候補所属、除去結果、末尾の分解証拠を `.next` へ渡すと、
列全体の分解証拠になる。

保証の対象は、部品の牌を順番どおりに連結した入力である。牌列を任意に並べ替えた場合は、この定理で
得た証拠を `MentsuPartition.of_perm` で移す。この役割分担により、ここでは除去順の議論を増やさずに済む。

ソース中の例は赤牌刻子1個について一般形の `partition` を作り、最後に `simpa` で `flatMap` を
具体的な `777z` の牌列へ計算している。

## 通常和了分割の実行器と宣言的仕様の一致を読む

次の実例は、`WaitCompletionFinder.lean` の `winningPartitions`、`WinningPartition`、
`mem_winningPartitions_iff` である。

読む前に知る語彙:

- `List.flatten`
- `List.map`
- `match`
- `inductive`
- `↔`
- 健全性と完全性
- `List.mem_flatten`
- `List.mem_map`
- `.mp` と `.mpr`
- `cases name : expression`
- `▸`

`winningPartitions tiles` は、牌種列を雀頭1つと完成面子列へ分解する方法をすべて列挙する実行器である。
各 `pairChunkCandidates` を雀頭として試し、実際に2枚を除けた枝だけを残す。その残り牌列を
`decomposeMentsu` で分解し、得られた各完成面子列の先頭へ雀頭を追加する。

`WinningPartition tiles chunks` は、特定の完成部品列 `chunks` が正しい通常和了分割であることを表す
宣言的仕様である。唯一の構築規則 `intro` は次の情報を要求する。

- `pair`: 分割結果の先頭に置く雀頭
- `pairCandidate`: その値が雀頭候補列に含まれる証拠
- `removePair`: 入力牌列から雀頭の2枚を除いた結果 `remaining`
- `mentsuPartition`: 残り牌列を完成面子列 `rest` へ分解する証拠

`intro` の結論は `WinningPartition tiles (pair :: rest)` なので、雀頭が必ず先頭に1つあり、
その後ろは順子・刻子だけになる。

`mem_winningPartitions_iff` は、実行器が `chunks` を列挙することと、この宣言的証拠を作れることが
同値だと示す。左から右の健全性により、実行器は不正な分割を返さない。右から左の完全性により、
正しい分割を実行器が取りこぼさない。

健全性方向では、外側の `flatten` と `map` の所属証拠から、選ばれた雀頭とその探索枝を取り出す。
`cases removeEq : removeTiles tiles pair.tiles` で除去結果を調べ、`none` の失敗枝には要素がないことを示す。
`some remaining` の成功枝では、内側の `map` から残りの完成面子列を取り出す。
あとは `mem_decomposeMentsu_iff` の健全性方向で面子分解証拠へ変換し、`WinningPartition.intro` を作る。

完全性方向では `WinningPartition.intro` に保存された情報を逆順に使う。面子分解証拠を
`mem_decomposeMentsu_iff` の完全性方向で実行器の列挙結果へ戻し、雀頭を追加する内側の `map`、
その雀頭を選ぶ外側の `map`、全枝をまとめる `flatten` への所属を順に組み立てる。

この上位証明は、面子分解の再帰をもう一度証明しない。`mem_decomposeMentsu_iff` を境界として再利用し、
新しく扱うのは雀頭候補の選択と除去だけである。

ソース中の例は、雀頭 `55m` と順子 `123m` を持つ `WinningPartition` の証拠を直接作り、同値定理の
`.mpr` 方向へ渡す。これにより、その完成部品列が `winningPartitions 55m123m` の実行結果へ実際に
含まれることをLeanが確認する。

## 通常和了分割が入力牌を保存することを読む

次の実例は、`WaitCompletionFinder.lean` の `WinningPartition.tiles_perm` である。

読む前に知る語彙:

- `inductive`
- inductive型のconstructor
- `cases`
- `List.flatMap`
- `List.Perm`
- `List.Perm.append_left`
- `.trans`

`WinningPartition.tiles_perm` の結論は、分割結果の全完成部品を牌種列へ戻して連結すると、入力牌列と
同じ牌種を同じ枚数だけ含むことである。前に読んだ `MentsuPartition.tiles_perm` が面子部分を保証し、
この定理はそこへ雀頭を加えて通常和了分割全体の保存則にする。

証明では `cases partition` により、`WinningPartition` の唯一の構築規則 `intro` に保存された情報を取り出す。
`removePair` と `exists_removeTiles_eq_some_iff_perm` から、`pair.tiles ++ remaining` が入力 `tiles` の
順列であるという `removedPerm` を得る。

一方、`mentsuPartition.tiles_perm` は、末尾の完成面子列を牌へ戻した列が `remaining` の順列であると保証する。
`List.Perm.append_left` で両側へ `pair.tiles` を加えると、雀頭を含む全完成部品の牌列と
`pair.tiles ++ remaining` の順列になる。これを `.trans removedPerm` で入力牌列までつなぐ。

ソース中の例は、雀頭 `55m` と順子 `123m` からなる分割を使う。入力側では `5m 1m 5m 2m 3m` と
牌が交互に並んでいるが、分割側では `55m` と `123m` にまとまる。両者は列として等しくなくても、
同じ牌を同じ枚数だけ持つことを `tiles_perm` から取り出せる。

## 通常和了分割が入力順に依存しないことを読む

次の実例は、`WaitCompletionFinder.lean` の `WinningPartition.of_perm` である。

読む前に知る語彙:

- `List.Perm`
- `cases`
- `obtain`
- `.trans` と `.symm`
- `List.Perm.length_eq`
- `rw [← ...] at ...`

定理は `WinningPartition tiles chunks` と `tiles.Perm other` から、同じ完成部品列 `chunks` を持つ
`WinningPartition other chunks` を作る。牌種と枚数が同じなら、入力牌列の順番を変えても通常和了分割の
証拠を保てるという主張である。

証明では `cases partition` により、雀頭 `pair`、元の除去結果 `remaining`、残りの面子分解証拠を取り出す。
`removePair` と `exists_removeTiles_eq_some_iff_perm` から得た `removedPerm` を、入力間の `permutation` と
つなぐと、並べ替え後の `other` からも同じ雀頭を除ける。

ただし、`removeTiles other pair.tiles` が返す残りは、元の `remaining` と同じ順番とは限らない。
同値定理から新しい残り `output`、除去成功 `removeOther`、`output.Perm remaining` をまとめて取り出す。
末尾の面子分解証拠は、前に読んだ `MentsuPartition.of_perm` で `remaining` から `output` へ移せる。

ここには添字付き命題による追加の型合わせがある。元の証拠が持つ面子数は
`remaining.length / mentsuTileCount` だが、新しい `WinningPartition` が要求する面子数は
`output.length / mentsuTileCount` である。順列は長さを保存するため、`outputPerm.length_eq` から
`output.length = remaining.length` を得る。`rw [← sameLength] at mentsuPartition` は、この等式で
証拠の型に現れる長さを書き換え、新しい残り牌列へ移せる形に揃える。

最後に、同じ雀頭候補、並べ替え後の除去結果、移送した面子分解証拠を `WinningPartition.intro` へ渡す。
ソース中の例は `55m123m` の分割証拠を、入力だけ並べ替えた `3m5m1m5m2m` へ移している。

## 待ち牌の実行器と宣言的仕様の一致を読む

次の実例は、`WaitCompletionFinder.lean` の `IsLegalTenpaiHand`、`IsWaitFor`、`waitingTiles`、
`mem_waitingTiles_iff`、`waitingTiles_ne_nil_iff` である。

読む前に知る語彙:

- `Prop`
- `Bool`
- `∧`
- `List.filter`
- `↔`
- 健全性と完全性
- `by_cases`
- `obtain`
- `rintro`
- `simp`
- `Bool.and_eq_true`

`IsLegalTenpaiHand tiles` は、待ち判定へ渡す手牌の事前条件をまとめる。通常形聴牌として扱う枚数が
1、4、7、10、13枚のいずれかであり、各牌種が物理的な上限の4枚を超えないことを要求する。

`IsWaitFor tiles candidate` は、候補牌が手牌 `tiles` の通常形待ちであるという宣言的仕様であり、
次の3条件を同時に要求する。

- 元の手牌が `IsLegalTenpaiHand` を満たす。
- 候補牌が手牌中に4枚未満しかなく、加牌しても5枚目にならない。
- 候補牌を先頭へ1枚加えた牌列が、雀頭1つと完成面子列からなる通常形で和了する。

`waitingTiles tiles` は同じ条件を計算する実行器である。まず合法手牌でなければ空列を返す。
合法なら全牌種 `Tile.all` を、4枚未満であることと加牌後に `isWinning` が真になることのBool論理積で
`filter` する。

`mem_waitingTiles_iff` は、候補牌がこの実行結果に含まれることと `IsWaitFor` を満たすことが同値だと示す。
したがって、列挙された牌が実際の通常形待ちであるという健全性と、仕様を満たす待ち牌を列挙が
取りこぼさないという完全性の両方が得られる。

証明は `by_cases legal : IsLegalTenpaiHand tiles` で、事前条件を満たす場合と満たさない場合に分ける。
非合法なら実行器は空列を返し、仕様の最初の条件も偽なので両辺は成立しない。

合法な場合は、`waitingTiles` と `IsWaitFor` の定義を `simp` で展開する。任意の牌種が `Tile.all` に
含まれることは `Tile.mem_all` で消え、`Bool.and_eq_true` が実行器の `&&` を2つの命題へ分解する。
残る条件は「4枚未満」と「加牌後に通常形で和了する」であり、`IsWaitFor` の残り2条件と一致する。

ソース中の例は、赤牌1枚の手牌について赤牌自身が単騎待ちとして `waitingTiles` に含まれることを示す。
同値定理の `.mpr` で目標を `IsWaitFor` へ変換し、具体的な有限計算を `native_decide` で確認する。
`unfold` は、この具体例で判定手続きが見えるように宣言的仕様を展開するために使っている。

`IsTenpai tiles` は、`IsWaitFor tiles candidate` を満たす牌種 `candidate` が少なくとも1つ存在するという、
牌姿全体の宣言的な聴牌仕様である。`waitingTiles_ne_nil_iff` は、待ち牌列挙の結果が空でないことと
`IsTenpai tiles` が同値だと示す。前の定理が個々の候補牌について健全性と完全性を保証したのに対し、
この定理はそれを「待ち牌が存在するか」という手牌単位の判定へ集約する。

左から右へは、空でない `waitingTiles tiles` から `List.exists_mem_of_ne_nil` で候補牌を1つ取り出し、
`mem_waitingTiles_iff` の `.mp` でその所属証拠を `IsWaitFor` の証拠へ変換する。右から左へは、
`IsTenpai` が持つ候補牌と待ちの証拠を `rintro` で取り出し、同値定理の `.mpr` で列挙結果への所属を得る。
列挙結果が空だと仮定するとその牌は所属できないため、矛盾する。

続く例は、赤牌1枚の手牌が意味論上も聴牌であることを確認する。ここでは具体的な列挙への所属を
`native_decide` で計算し、`List.ne_nil_of_mem` で列挙結果が空でないことへ変え、
`waitingTiles_ne_nil_iff` によって `IsTenpai` の証明として受け取る。この流れにより、有限な実行結果が
宣言的な聴牌仕様の証拠になることを小さな入力で確かめられる。

## 待ちと和了分割を返すFinderの正しさを読む

次の実例は、`WaitCompletionFinder.lean` の `findWaitCompletions`、`CompletionFor`、
`mem_findWaitCompletions_iff` である。

読む前に知る語彙:

- `List.flatMap`
- `List.map`
- `List.dedup`
- `List.mem_dedup`
- `List.mem_flatMap`
- `List.mem_map`
- 添字付き帰納型
- 健全性と完全性
- `obtain`
- `cases`
- `refine`

`findWaitCompletions tiles` は、単に待ち牌だけでなく、その牌を加えたときの通常和了分割も返す実行器である。
まず `waitingTiles tiles` の各待ち牌について `winningPartitions` を実行し、待ち牌と分割を
`WaitCompletion` にまとめる。分割内の部品順を `TileChunk.canonicalize` で標準化し、最後に `dedup` で
同じ結果の重複を除く。

`CompletionFor tiles completion` は、返り値 `completion` の宣言的仕様である。その証拠は、
`IsWaitFor tiles wait` を満たす待ち牌と、加牌後の牌列に対する `WinningPartition` を持つ。
一方、返り値に記録される分割は正規化済みであるため、仕様は正規化前の `rawChunks` が存在し、
`completion.winningChunks` がその標準順表現になるという形を帰納型の結論で表している。

`mem_findWaitCompletions_iff` は、Finderの結果への所属と `CompletionFor` が同値だと示す。
これは `mem_waitingTiles_iff` と `mem_winningPartitions_iff` という二つの下位境界を合成した、
探索全体の健全性・完全性である。Finderが返した組には正しい待ち牌と和了分割が必ずあり、逆に、
仕様を満たす組はFinderの結果に必ず含まれる。

証明冒頭の `rw [findWaitCompletions, List.mem_dedup]` は実行器を展開し、重複除去後への所属を
重複除去前への所属に直す。健全性方向では、`List.mem_flatMap.mp` が結果を生成した待ち牌を、
`List.mem_map.mp` が正規化前の分割を取り出す。それぞれの所属を下位の同値定理の `.mp` で
`IsWaitFor` と `WinningPartition` へ変換し、`CompletionFor.intro` に渡す。

完全性方向では `cases valid` により仕様の証拠から待ち牌、分割、二つの正しさの証拠を取り出す。
下位定理の `.mpr` でそれらを実行結果への所属へ戻し、`List.mem_map.mpr` と
`List.mem_flatMap.mpr` を使ってFinder全体への所属を組み立てる。両方向で同じ二つの境界定理を
逆向きに使う構造が、過不足のなさを直接表している。

ソース中の例は、赤牌1枚の単騎待ちについて、赤牌を加えた対子分割を持つ `WaitCompletion` が
`CompletionFor` を満たすことを示す。具体的なFinderへの所属は `native_decide` で計算し、
同値定理の `.mp` によって宣言的な正しさの証拠へ変換する。

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

次の実例は、`Wait/Analysis.lean` の `reducibility`、`determineReducibility`、`reducibility_eq_reducible_iff`、
`reducibility_eq_irreducible_iff` である。

先に [domain-vocabulary.md](domain-vocabulary.md) の「待ち核集合」と「可約と既約」を読む。

読む前に知る語彙:

- `def`
- `if`
- 証拠付き `if`
- `Option`
- `theorem`
- `↔`
- `¬`
- `simp`

`reducibility` は、聴牌であることが確認済みの牌列について、待ち核集合を変えずに完成面子を除去できるかを調べる。
除去できれば `reducible`、できなければ `irreducible` を返す。

`determineReducibility` は、聴牌かまだ分からない一般の牌列に対する入口である。
聴牌なら条件分岐で得た証拠を `reducibility` へ渡して結果を `some` に包み、非聴牌なら `none` を返す。
したがって `none` は解析失敗や既約を意味するのではなく、可約性を分類する前提である聴牌を満たさないことを表す。

`reducibility_eq_reducible_iff` は、計算結果が `reducible` であることと、実際に待ち核集合を保つ面子除去が
可能であることが同値だと保証する。左から右は誤って可約と判定しないこと、右から左は可能な面子除去を
見落とさないことに対応する。

証明の `simp [reducibility]` は、`reducibility` の条件分岐を展開し、その判定条件が右辺の命題
`CanReduceMentsuPreservingWaitCores` そのものであることを確認する。

`reducibility_eq_irreducible_iff` は対になる保証で、計算結果が `irreducible` であることを、待ち核集合を
保ったまま除去できる完成面子がないこととして特徴づける。既約性のために別の探索をするのではなく、
可約性を表す同じ命題の否定 `¬CanReduceMentsuPreservingWaitCores` を使っている点を読む。

## Readingから核成分列を分離する処理を読む

次の実例は、`WaitReadingCode.lean` の `ConcreteWaitReading`、`IrreducibleWaitReading`、
`reduceWaitReading` である。

先に [domain-vocabulary.md](domain-vocabulary.md) の「Reading」と「待ち核」を読む。

読む前に知る語彙:

- `structure`
- `filter`
- `fun`
- `!`

`ConcreteWaitReading` は、1つの待ち牌と、待ち牌を除いた和了分割に見える具体牌付き部品列を持つ。
この段階では、不完全部品と、すでに完成している順子・刻子が同じ `components` に並んでいる。

`reduceWaitReading` は、順子と刻子を `removedMentsu` に分離し、それ以外を `core` に残して
`IrreducibleWaitReading` を作る。2つの `filter` は同じ部品列を反対の条件で選別しており、
待ち牌と各部品の具体牌は変更しない。

最初は、待ち牌 `4m` に対して、部品列が「単騎 `4m`、完成順子 `123p`」である1つのReadingだけを考える。
`reduceWaitReading` を適用すると、単騎 `4m` は `core` に残り、完成順子 `123p` は `removedMentsu` に入る。
スートが異なるため別の分解を考える必要がなく、ここでは2つの `filter` による振り分けだけを読めばよい。

名前に `Irreducible` とあるが、`reduceWaitReading` 自体は1つのReadingから完成面子を分離する局所処理であり、
牌姿全体が可約か既約かは判定しない。牌姿全体の判定では、そこから得られる待ち核集合を、完成面子除去の
前後で比較する必要がある。複数の分解を持つ `1234m` は、その段階で扱う例である。

## 分離結果から待ち核集合を作る処理を読む

次の実例は、`WaitReadingCode.lean` の `WaitCore` と `waitCores` である。

先に [domain-vocabulary.md](domain-vocabulary.md) の「待ち核」と「待ち核集合」を読む。

読む前に知る語彙:

- `map`
- `fun`
- `|>`
- `List`

`waitCores` は、発見済みの全Readingから `IrreducibleWaitReading` を作り、それぞれを `WaitCore` に変換する。
この変換では、待ち牌 `wait` と核成分列 `core` を残し、どの完成面子を分離したかを表す `removedMentsu` は忘れる。
これにより、異なる和了分割から同じ待ち牌と核成分列が得られた場合、それらを同じ待ち核として比較できる。

前節の「単騎 `4m`、完成順子 `123p`」というReadingなら、待ち核には待ち牌 `4m` と単騎 `4m` だけが残り、
分離した順子 `123p` は含まれない。

最後の `deduplicateAndSortBy` は、同じ待ち核の重複を除き、一定の順序に整列する。
したがって返り値の型は `List WaitCore` だが、コード上では重複を除いて整列したリストを有限の待ち核集合として使う。

## 待ち核集合を保つ面子除去を読む

次の実例は、`WaitReadingCode.lean` の `canReduceMentsuPreservingWaitCores`、
`CanReduceMentsuPreservingWaitCores` と、その `Decidable` インスタンスである。

先に [domain-vocabulary.md](domain-vocabulary.md) の「待ち核集合」と「可約と既約」を読む。

読む前に知る語彙:

- `Bool`
- `&&`
- `!`
- `List.any`
- `==`
- `Prop`
- `Decidable`

`mentsuReductions tiles` は、牌列から完成面子を1つ取り除いて得られる候補を列挙する。
`canReduceMentsuPreservingWaitCores` は、その候補の中に次の2条件を両方満たすものがあるかを調べる。

- 除去後の牌列にも待ち牌があり、聴牌形として残っている。
- 除去前後で `findWaitCores` が返す待ち核集合が一致する。

除去後の聴牌を別に確認するため、待ちのない牌列どうしで空の待ち核集合が一致しただけでは可約にならない。
また、`1 < tiles.length` により、完成面子を含み得ない1枚単騎は最初に除外する。

結果が `true` なら、元の牌姿には待ち核集合を変えずに分離できる完成面子が少なくとも1つある。
どの候補が成功したかではなく、そのような候補が存在するかだけを返す判定である。

先頭が小文字の `canReduceMentsuPreservingWaitCores` は、実際に実行して `true` または `false` を返す。
先頭が大文字の `CanReduceMentsuPreservingWaitCores` は、その結果が `true` であることを表す `Prop` である。
大文字側で別の条件を追加しているわけではなく、同じ計算結果を定理の仮定や結論として使える形にしている。

直後の `Decidable` インスタンスは、この命題が小文字側のBool計算によって判定できることをLeanへ登録する。
これにより、`Analysis.lean` の `reducibility` は `CanReduceMentsuPreservingWaitCores tiles` を `if` の条件にでき、
後続の同値定理では同じ名前を可約性の意味として使える。

## 完成部品から待ち牌を除いた形を読む

次の実例は、`WaitReadingCode.lean` の `componentKindAfterRemovingWait` と `componentAfterRemovingWait` である。

先に [domain-vocabulary.md](domain-vocabulary.md) の「和了分割の完成部品」を読む。

読む前に知る語彙:

- `Option`
- `match`
- `if`
- `==`
- `!=`
- `Option.map`
- `List.erase`
- `example`
- `rfl`

この関数は、1つの和了分割の完成部品 `TileChunk` と指定した待ち牌を受け取り、その牌を1枚除いたときに見える
不完全部品の種別を返す。最初は次の単純な対応を読む。

- 対子 `55m` から `5m` を除くと、単騎 `5m` が残る。
- 刻子 `777p` から `7p` を除くと、対子 `77p` が残る。

順子では、除く牌の位置によって残るターツが変わる。

- 順子 `234s` から `2s` を除くと `34s` が残り、両面になる。
- 順子 `234s` から `3s` を除くと `24s` が残り、嵌張になる。
- 順子 `123s` から `3s` を除くと `12s` が残り、辺張になる。

ソース中の `example` は、この5つの対応をLeanの計算で確認する。
指定牌が対子・刻子と同じ牌種でない場合、または順子とスートやランクが合わない場合は `none` を返す。
ここでの `none` は待ち全体が存在しないという意味ではなく、この1つの完成部品から指定牌を除く形を作れないという意味である。

`componentAfterRemovingWait` は、その種別判定に具体的な牌の除去を加える。
種別が得られた場合だけ `List.erase` で待ち牌を最初の1枚だけ除き、種別と残った牌種列を
`ConcreteWaitReadingComponent` にまとめる。種別が `none` なら、`Option.map` により結果も `none` のままになる。

対子 `55m` と待ち牌 `5m` の例では、種別は単騎、残った牌種列は `[5m]` になる。
この対応もソース中の `example` が `rfl` で確認している。

## 和了分割からReadingを列挙する処理を読む

次の実例は、`WaitReadingCode.lean` の `waitReadings` である。

先に [domain-vocabulary.md](domain-vocabulary.md) の「和了分割の完成部品」と「Reading」を読む。

読む前に知る語彙:

- `let rec`
- `match`
- `[]`
- `::`
- `map`

`WaitCompletion` は、1つの待ち牌と、その牌を加えた和了分割を持つ。
`waitReadings` は分割の完成部品を先頭から調べ、待ち牌を除ける部品を1つ選んで不完全部品へ変える。
選ばなかった部品は、対子・順子・刻子という完成した種別のままReadingに残す。

最初は、待ち牌が `5m`、和了分割が雀頭 `55m` と順子 `123p` からなる例を読む。
待ち牌を除けるのは雀頭だけなので、結果は「単騎 `5m`、完成順子 `123p`」という1つのReadingになる。
ソース中の `example` は、この列挙結果を `rfl` で確認する。

同じ待ち牌を除ける完成部品が複数ある場合は、どの部品を除去元として選ぶかごとに別のReadingを返す。
つまり、この処理は1つの分割を決め打ちで読むのではなく、その分割から生じるすべての観測結果を列挙する。

## 複数の和了分割から具体的なReadingをまとめる

次の実例は、`WaitReadingCode.lean` の `concreteWaitReadings` である。

読む前に知る語彙:

- `let`
- `flatMap`
- `map`
- `structure`

`concreteWaitReadings` は、複数の `WaitCompletion` に前節の `waitReadings` を適用し、すべての結果を
待ち牌と具体牌付き部品列を持つ `ConcreteWaitReading` にまとめる。

和了分割は、同じ部品を異なる順序で持つことがある。そのままでは部品順だけが異なるReadingが別物に見えるため、
各Readingの部品列を `canonicalizeWaitReading` で一定の順序に並べる。最後に
`deduplicateAndSortBy` が同一Readingの重複を除き、結果全体も一定の順序へ整える。

ソース中の `example` は、雀頭 `55m` と順子 `123p` の順序だけを入れ替えた2つのcompletionを入力する。
どちらからも同じ「単騎 `5m`、完成順子 `123p`」が得られるため、部品順を整列して重複を除いた結果は1件だけになる。
これにより、データ上の部品順や重複ではなく、観測される待ち牌と部品の内容を比較できる。

## 具体牌を忘れて抽象Readingを作る

次の実例は、`WaitReadingCode.lean` の `AbstractWaitReading` と `abstractWaitReadings` である。

先に [domain-vocabulary.md](domain-vocabulary.md) の「Reading」を読む。

読む前に知る語彙:

- `map`
- `fun`
- `|>`

`abstractWaitReadings` は、各 `ConcreteWaitReading` の待ち牌を保持したまま、具体牌付き部品を
その部品種別 `kind` だけに変換する。単騎がどの牌だったか、完成順子がどのスート・ランクだったかは忘れるが、
待ち牌と「単騎、順子」のような部品種別列は残る。

ソース中の `example` では、待ち牌がどちらも `5m` で、完成順子だけが `123p` と `456p` で異なる
2つの具体Readingを作る。具体牌を忘れると、どちらも部品種別列 `[tanki, shuntsu]` になるため、
重複排除後の抽象Readingは1件になる。

この段階では部品種別列を数値へ変換しない。次の `waitReadingCodeEntries` が、抽象Readingを
待ち牌と素数積コードの組へ変換する。

## 抽象Readingを素数積コードへ変換する

次の実例は、`WaitReadingCode.lean` の `WaitReadingComponentKind.prime`、`componentProduct`、
`WaitReadingCodeEntry`、`waitReadingCodeEntries` である。

先に [domain-vocabulary.md](domain-vocabulary.md) の「待ちReadingコード」を読む。

読む前に知る語彙:

- `Nat`
- `List.foldl`
- `map`
- `|>`

各部品種別には異なる素数が割り当てられている。たとえば単騎は2、順子は13である。
`componentProduct` は1から始めて、抽象Readingの各部品に対応する素数を順に掛ける。

積では掛ける順序が結果に影響しないため、部品列の順序は忘れられる。一方、同じ部品が複数あれば
同じ素数を繰り返し掛けるため、その個数は指数として残る。たとえば `[tanki, shuntsu]` は
$2 \times 13 = 26$、`[tanki, shuntsu, shuntsu]` は $2 \times 13^2 = 338$ になる。

`waitReadingCodeEntries` は、計算したコードだけでなく待ち牌も `WaitReadingCodeEntry` に残す。
ソース中の `example` は、待ち牌 `5m` と部品種別 `[tanki, shuntsu]` から
`{ wait := 5m, code := 26 }` が得られることを計算で確認する。

## Readingコードを待ち牌付きのペアで取り出す

次の実例は、`WaitReadingCode.lean` の `abstractWaitReadingCodeWithWait` である。

読む前に知る語彙:

- 直積 `×`
- `map`
- `fun`

`abstractWaitReadingCodeWithWait` は、`WaitReadingCodeEntry` を `(コード, 待ち牌)` のペアへ変換する。
部品種別列からコードを計算する処理は前節で完了しているため、ここではフィールドを取り出して並べ替えるだけである。

前節と同じ、待ち牌 `5m`、部品種別 `[tanki, shuntsu]` の例なら、結果は `(26, 5m)` になる。
待ち牌を保持しているため、複数の待ち牌が同じコードを持っていても、それぞれを別のペアとして確認できる。

名前に `WithWait` が付くのは、この待ち牌情報を残すためである。
後続の `abstractWaitReadingCode` は待ち牌を捨て、コードの種類だけを列挙するので区別して読む。

## 待ち牌を忘れてコードの種類だけを取り出す

次の実例は、`WaitReadingCode.lean` の `abstractWaitReadingCode` である。

先に [domain-vocabulary.md](domain-vocabulary.md) の「待ちReadingコード」を読む。

読む前に知る語彙:

- `map`
- `|>`

`abstractWaitReadingCode` は、待ち牌付きの各entryから `code` だけを取り出す。
この変換後は、異なる待ち牌でも部品種別コードが同じなら同じ自然数になるため、重複をもう一度除いて整列する。

ソース中の `example` では、待ち牌 `5m` と `6m` がそれぞれ単騎と完成順子からなるReadingを持つ。
待ち牌は異なるが、どちらの部品種別列も `[tanki, shuntsu]` なのでコードは26であり、結果は `[26]` になる。

この表現は、コード系列の中で最も多くの情報を忘れている。
コード列が一致しても、待ち牌、具体的な部品の牌、元の牌姿が同じとは限らない。
さらに現行実装は重複も除くため、「その組合せを持つReadingがいくつあるか」も分からない。
たとえば `2345678m` の3つの待ち牌がすべてコード338でも、結果は `[338]` になる。

この重複排除は仕様変更の検討対象である。重複を保った `[338, 338, 338]` からは必要に応じて `[338]` を
導出できるが、`[338]` から3つのReadingがあったことは復元できない。現行関数は、暫定的に
「どの部品種別の組合せが少なくとも1回現れるか」だけを比較する集計として読む。
