import Mahjong.Pattern

/-!
# 待ちと和了分割

`Shape` は、1つの待ち牌と、その牌を加えたときの通常形の和了分割を表す。
牌列から `Shape` を見つける処理は `ShapeFinder`、見つかった形の符号化は
`ShapeCode` が担当する。
-/

namespace TileChunk

private def suitKey : Suit → Nat
  | .Manzu => 0
  | .Pinzu => 1
  | .Souzu => 2

private def honorKey : Honor → Nat
  | .East => 0
  | .South => 1
  | .West => 2
  | .North => 3
  | .White => 4
  | .Green => 5
  | .Red => 6

private def tileKey : Tile → Nat
  | .numbered suit rank => suitKey suit * 9 + rank.val
  | .honor honor => 27 + honorKey honor

private def orderKey : TileChunk → Nat
  | .inl (.toitsu tile) => tileKey tile
  | .inr (.shuntsu (.shuntsu suit start)) => 34 + suitKey suit * 7 + start.val
  | .inr (.koutsu tile) => 55 + tileKey tile

/-- 分割内の部品順を一意にする。 -/
def canonicalize (chunks : List TileChunk) : List TileChunk :=
  chunks.mergeSort fun first second => orderKey first ≤ orderKey second

end TileChunk

/-- 1つの待ち牌と、その牌を加えた和了形の1つの分割。 -/
structure Shape where
  wait : Tile
  chunks : List TileChunk
deriving BEq, DecidableEq, Repr
