# Lean未経験者向けの読む順番

この文書は、Leanを知らない読者が麻雀待ち分類の成果と正しさを追うための読み順を定める。
Leanの構文説明をすべてソースコメントに詰め込まず、必要な語彙を先に導入してから定義や定理を読む。

## 基本方針

文章は1次元にしか読めないため、コード上の依存関係と説明上の依存関係を分けて扱う。

- コード上の依存関係: Leanファイルがどの定義や定理を使っているか。
- 説明上の依存関係: 読者がその説明を理解するために先に知るべき概念や語彙。

読書体験では、説明上の依存関係を優先する。同じLean語彙の説明を各定理で繰り返さず、初出時に
[lean-vocabulary.md](lean-vocabulary.md) へ集約する。

## 最初の入口

1. [lean-vocabulary.md](lean-vocabulary.md) の「最小語彙」を読む。
2. `Mahjong/Basic.lean` の牌種定義を読む。
3. `Tile.all` が34種類の牌種一覧であることを読む。
4. `Tile.mem_all` が、その一覧に抜けがないことを保証していることを読む。

この段階では、証明の細部をすべて追う必要はない。まずは「どの一覧に対して、何を保証しているか」を
理解する。

## その後の予定

次に読む実例は、待ち分類語彙の一覧性を示す `WaitKind.exhaustive` である。ここでは
`Tile.mem_all` と同じく、列挙した分類名に抜けがないことを確認する読み方を使う。

読む前に知る語彙:

- `namespace`
- `theorem`
- `cases`
- `<;>`
- `simp`
- `[...]`
- `∈`

`Tile.mem_all` では牌種の一覧を確認した。`WaitKind.exhaustive` では、待ち分類名の一覧を確認する。
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
