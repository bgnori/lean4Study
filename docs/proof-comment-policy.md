# 証明コメント方針

この文書は、Leanソース内の定義・定理コメントと、外部ドキュメントの役割分担を定める。

## 役割分担

ソースコメントは局所説明、docsは線形化された読書体験、語彙ページは重複回避の辞書として使う。

- ソースコメント: その定義や定理が麻雀待ち分類の中で何を意味するかを書く。
- [reading-order.md](reading-order.md): Lean未経験者が読む順番を示す。
- [lean-vocabulary.md](lean-vocabulary.md): Lean語彙の初出説明を集約する。

## 定理コメントに書くこと

定理コメントには、次の内容を優先して書く。

- 何を保証している定理か。
- その保証が、麻雀待ち分類の正しさのどこを支えるか。
- 証明の大まかな考え方。
- 読むために必要なLean語彙名。

## 定理コメントに書きすぎないこと

次の内容は、原則として [lean-vocabulary.md](lean-vocabulary.md) に集約する。

- `namespace`、`theorem`、`by` などの一般的な構文説明。
- `cases`、`simp`、`left`、`exact` などのタクティク説明。
- `[...]`、`∈`、`++` などの記号の一般説明。

ただし、その定理での使われ方が読解の鍵になる場合は、短く補足してよい。

## まとまりを説明するコメント

1つの定義を複数の小さな定理で支える場合や、関連する処理を数個並べる場合は、定理コメントだけで全体像を説明しようとしない。
定義の直前に section comment を置き、定義と定理群の関係を説明する。

- section comment: 定義が何をし、どの定理がどの側面を保証するかを書く。
- definition comment: 入力と返り値を短く説明する。
- theorem comment: その定理が保証する一点と、証明の大まかな考え方を書く。

まだ仕様定理がない処理群でも、読者が処理のまとまりを理解するために section comment を置いてよい。
その場合は「どの入力から何を探すか」「失敗をどう表すか」「どの関数が入口か」を優先して書く。

麻雀上の概念とLean上のデータ構造の対応が前提になる箇所では、定理より先に概念対応の section comment を置く。
その場合は「麻雀での意味」「Leanでの型」「共通インターフェースへの接続」を優先して書く。
読者が牌姿を具体的に見たほうが理解しやすい箇所では、`Tile.format .mpsz` を使った `example` を添える。
この `example` は説明用サンプルであると同時に、Leanが検査する小さな仕様として扱う。
補助的な `def` や `abbrev` が続く箇所では、個別コメントを厚くするより、section comment で「何のための補助群か」を先に説明する。

## `Tile.mem_all` の粒度例

よい粒度の例:

```lean
/--
すべての牌種は標準列挙 `Tile.all` に含まれる。

この定理は、以降の網羅的な探索や分類が参照する「34種類の牌の一覧」に抜けがないことを保証する。
証明は `Tile` を数牌と字牌に分け、それぞれが対応する一覧に含まれることを示す。

読むためのLean語彙: `namespace`, `theorem`, `cases`, `simp`, `left`, `exact`, `∈`。
-/
```

このコメントでは、定理固有の意味を説明し、Lean語彙の詳細説明は語彙ページに任せる。

## `WaitKind.exhaustive` の粒度例

よい粒度の例:

```lean
/--
すべての待ち分類名は標準列挙 `WaitKind.all` に含まれる。

この定理は、通常形聴牌で使う分類語彙の一覧に抜けがないことを保証する。
証明は `WaitKind` の各分類名に場合分けし、それぞれが明示的な一覧に含まれることを示す。

読むためのLean語彙: `namespace`, `theorem`, `cases`, `<;>`, `simp`, `[...]`, `∈`。
-/
```

この例では、新しく出てくる `<;>` の詳細説明をソースコメントではなく語彙ページに置く。

## `deck_cardinality` の粒度例

よい粒度の例:

```lean
/--
麻雀牌の山は `deckSize` 枚、つまり34種類それぞれを `copiesPerTile` 枚ずつ含む。

この定理は、物理牌として扱う山の枚数が通常の麻雀牌の総数と一致することを保証する。
証明では `deck` の定義を展開し、有限型 `PhysicalTile` 全体の個数が `Tile.count * copiesPerTile`
になることを確認する。

読むためのLean語彙: `abbrev`, `Finset`, `.card`, `theorem`, `simp`, `rfl`。
-/
```

この例では、麻雀上の「山の枚数」とLean上の「有限集合の要素数」を対応させる説明に集中する。

## `Chunk.take` の仕様ブロック例

よい粒度の例:

```lean
/-!
## `Chunk.take` の基本仕様

`Chunk.take` は、空でない牌集合 `chunk` から、そこに含まれることが分かっている物理牌
`tile` を1枚取り出す。返り値は `(取り出した牌, 残りの牌集合)` というペアである。

この仕様は、次の2つの定理で確認する。

- `take_fst`: 返り値の1番目は、指定した `tile` そのものである。
- `take_snd_not_mem`: 返り値の2番目、つまり残りの集合には、取り出した牌はもう含まれない。
-/

/--
`chunk.take tile` の返り値の1番目は、指定した `tile` そのものである。

証明は `take` の定義をそのまま見ると左右が同じ形になるため、`rfl` で終わる。

読むためのLean語彙: `.1`, `@[simp]`, `theorem`, `rfl`。
-/
```

この例では、関数全体の仕様を section comment で説明し、個々の定理コメントは保証する一点に絞る。

## `takeTileFrom` から `takeTiles` までの処理ブロック例

よい粒度の例:

```lean
/-!
## 牌種列から物理牌を取り出す処理

`Chunk.take` は、すでに `chunk.tiles` に含まれると分かっている物理牌を1枚取り出した。
ここからは、牌種 `Tile` を指定して、それに対応する物理牌を探して取り出す。

- `takeTileFrom`: 有限集合から、指定した牌種を持つ物理牌を1枚探して取り出す。
- `takeTilesFrom`: 牌種列を順に処理し、対応する物理牌列を取り出す。
- `takeTiles`: `Chunk` に対する薄い入口。

これらは `noncomputable def` である。数学的な定義として使えるが、Leanが通常の実行用コードとして
扱う計算可能な定義とは区別して読む。
-/
```

この例では、定理がまだない処理群も読解単位としてまとめる。

## `HasTilePattern` の抽象化ブロック例

よい粒度の例:

```lean
/--
「この型の値は、対応する牌種列を持つ」ことを表す型クラス。

`WaitPattern` や面子候補のように、具体的な型は違っても「必要な牌種列」を取り出せるものを、
同じ物理牌取り出し処理に渡すための小さな共通インターフェースである。

読むためのLean語彙: `class`, 型引数, 型クラス引数。
-/
class HasTilePattern (α : Type) where
  tiles : α → List Tile

namespace HasTilePattern

/-!
## 牌種パターンから物理牌を取り出す共通処理

`HasTilePattern` のインスタンスを持つ型なら、`HasTilePattern.tiles` で牌種列を取り出せる。
`HasTilePattern.take` は、その牌種列を `Chunk.takeTiles` に渡して、対応する物理牌を取り出す。

`namespace HasTilePattern` の内側で定義することで、この処理を `HasTilePattern.take` という名前で参照できる。
-/
```

この例では、証明ではなく抽象化の意図を説明する。どの具体型に使うか、どの既存処理へ接続するかを明示する。

## `MentsuCandidate.mem_candidates` の粒度例

この定理を読む前に、`Pattern.lean` の小部品が何を表すかを section comment で説明する。

```lean
/-!
## 待ち分類で使う小さな牌パターン

ここからは、麻雀上の部品をLeanのデータ構造として定義する。

- `Taatsu`: 両面・嵌張・辺張のような、完成まであと1枚の2枚組。
- `Toitsu`: 同じ牌種2枚からなる対子。
- `Tanki`: 単騎待ちの核になる1枚。
- `Shuntsu`: 同じスートで連続する3枚からなる順子。
- `MentsuCandidate`: 通常形で完成面子として扱う候補。順子または刻子。

これらは後で物理牌を取り出せるように、それぞれ `tiles` で必要な牌種列を返し、
`HasTilePattern` のインスタンスを持つ。
-/
```

ターツ、対子、単騎、順子、刻子のように具体例が有効な定義では、`Tile.format .mpsz` を使った `example` を近くに置く。

```lean
example : (Taatsu.ryanmen .Manzu ⟨0, by decide⟩).tiles.map (Tile.format .mpsz) = ["2m", "3m"] := rfl
example : (Taatsu.kanchan .Pinzu ⟨2, by decide⟩).tiles.map (Tile.format .mpsz) = ["3p", "5p"] := rfl
example : (Taatsu.penchan .Souzu false).tiles.map (Tile.format .mpsz) = ["1s", "2s"] := rfl
example : (Taatsu.penchan .Souzu true).tiles.map (Tile.format .mpsz) = ["8s", "9s"] := rfl
example : (Toitsu.toitsu (.numbered .Manzu 4)).tiles.map (Tile.format .mpsz) = ["5m", "5m"] := rfl
example : (Tanki.tanki (.numbered .Pinzu 2)).tiles.map (Tile.format .mpsz) = ["3p"] := rfl
example : (Shuntsu.shuntsu .Souzu ⟨0, by decide⟩).tiles.map (Tile.format .mpsz) = ["1s", "2s", "3s"] := rfl
example : (MentsuCandidate.koutsu (.numbered .Pinzu 6)).tiles.map (Tile.format .mpsz) = ["7p", "7p", "7p"] := rfl
```

よい粒度の例:

```lean
/--
任意の完成面子候補は、実行用候補列 `MentsuCandidate.candidates` に含まれる。

この定理は、完成面子候補を列挙して調べる処理が、順子候補と刻子候補を取りこぼさないことを保証する。
証明では候補を順子の場合と刻子の場合に分ける。順子の場合はスートと開始位置から作った順子候補列に
含まれることを示し、刻子の場合は `Tile.mem_all` を使って、刻子に使う牌種が標準牌種列に含まれることを示す。

読むためのLean語彙: `inductive`, `namespace`, `theorem`, `cases`, `rcases`, `simp`, `left`, `refine`, `?_`, `exact`, `∈`。
-/
```

この例では、以前に説明した列挙網羅性の定理 `Tile.mem_all` が、より大きな候補列の網羅性に使われることを明示する。

## `MentsuCandidate.honor_not_in_shuntsu` の粒度例

よい粒度の例:

```lean
/--
字牌を含む完成面子候補は順子ではない。

この定理は、順子が同じスートの連続する数牌だけからなる、という麻雀上の制約をLean上の
`MentsuCandidate` に対して確認する。候補が刻子なら順子ではない。候補が順子なら、
`Shuntsu.tiles` は数牌だけを返すため、字牌が含まれるという仮定と矛盾する。

読むためのLean語彙: `Prop`, `theorem`, `∈`, `¬`, `cases`, `simp`, `at`。
-/
```

この例では、麻雀上の制約がLean上のデータ構造ではどの定義に現れているかを明示する。

## 補助定義と `TileChunk` のブロック例

補助的な `def` が続く箇所では、読者がその後の概念に進むための足場としてまとめる。

```lean
/-!
## 通常形のサイズと数牌の開始位置

ここでは、後続の牌パターン定義で使う小さな数値を名前付きで定義する。
通常形の手牌枚数は、面子数に3枚を掛け、雀頭1組を足して計算する。

両面ターツや順子は、開始位置を `Fin` で表す。`Fin n` は `0` 以上 `n` 未満の値なので、
存在しない開始位置を型で除外できる。
-/
```

`TileChunk` のように複数の概念を1つの型へまとめる箇所では、どの概念を合流させているかを明示する。

```lean
/-!
## 雀頭と完成面子を同じ完成部品として扱う

通常形の和了分割では、雀頭と完成面子をどちらも「完成した部品」として並べて扱う。
`TileChunk` は、雀頭 `Toitsu` または完成面子候補 `MentsuCandidate` のどちらかを持つ型である。

`pair`、`shuntsu`、`koutsu` は、麻雀上の呼び名から `TileChunk` を作る入口である。
`TileChunk.tiles` は、どちらの部品であっても構成する牌種列を返す。
-/
```

## `WaitPattern` の読解ブロック例

待ち分類に入る箇所では、「実際に待ちであること」と「終端部をどう抽出するか」を混同しないように説明する。
麻雀一般の「待ち読み」と衝突しやすいため、`WaitPattern` の説明では原則として「読み」ではなく「抽出パターン」を使う。

```lean
/-!
## 待ち終端の抽出パターン

`WaitPattern` は、手牌から最後に残る1枚または4枚の終端部を、どの形として抽出するかを表す。
ここでは麻雀一般の「待ち読み」という語を避け、抽出に使うデータ構造として扱う。
実際に待ちであることの証明は `WaitCompletionFinder.IsWaitFor` が担当する。

- `tanki`: 単騎として扱う1枚と、同じ4枚終端に残る面子候補を組み合わせる。
- `toitsuRyanmen`: 対子と両面ターツからなる4枚終端。
- `toitsuKanchan`: 対子と嵌張ターツからなる4枚終端。
- `toitsuPenchan`: 対子と辺張ターツからなる4枚終端。
- `shanpon`: 2つの対子からなる4枚終端。

`tanki` が面子候補を持つのは、4枚終端を抽出するためであり、その牌姿が既約であることは意味しない。
完成面子を取り除けるかどうかは、後続の `WaitReducibility` で別に扱う。

`WaitPattern.tiles` は、その抽出パターンで必要になる牌種列を返す。
-/
```

具体例が有効なため、`WaitPattern.tiles` の近くに `Tile.format .mpsz` を使った `example` を置く。
