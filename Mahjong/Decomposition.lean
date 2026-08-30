import Mahjong.Basic
import Mahjong.Pattern

/-!
# 待ちと和了分割

`Decomposition` は、1つの待ち牌と、その牌を加えたときの通常形の和了分割を表す。
牌列から `Decomposition` を見つける処理は `DecompositionFinder`、見つかった形の符号化は
`DecompositionCode` が担当する。
-/

namespace TileChunk

private def orderKey : TileChunk → Nat
  | .inl (.toitsu tile) => tile.orderKey
  | .inr (.shuntsu (.shuntsu suit start)) =>
      Tile.count + suit.orderKey * shuntsuStartCount + start.val
  | .inr (.koutsu tile) => Tile.count + Suit.count * shuntsuStartCount + tile.orderKey

/-- 分割内の部品順を一意にする。 -/
def canonicalize (chunks : List TileChunk) : List TileChunk :=
  chunks.mergeSort fun first second => orderKey first ≤ orderKey second

end TileChunk

/-- 1つの待ち牌と、その牌を加えた和了形の1つの分割。 -/
structure Decomposition where
  wait : Tile
  chunks : List TileChunk
deriving BEq, DecidableEq, Repr
