import Mahjong.Basic
import Mahjong.Pattern

/-!
# 待ちと和了分割

`WaitCompletion` は、1つの待ち牌と、その牌を加えたときの通常形の和了分割を表す。
牌列から `WaitCompletion` を見つける処理は `WaitCompletionFinder`、見つかった形の符号化は
`WaitReadingCode` が担当する。
-/

namespace TileChunk

private def orderKey : TileChunk → Nat
  | .inl (.toitsu tile) => tile.orderKey
  | .inr (.shuntsu (.shuntsu suit start)) =>
      Tile.count + suit.orderKey * shuntsuStartCount + start.val
  | .inr (.koutsu tile) => Tile.count + Suit.count * shuntsuStartCount + tile.orderKey

/-- 分割内の部品順を一意にする。 -/
def canonicalize (winningChunks : List TileChunk) : List TileChunk :=
  winningChunks.mergeSort fun first second => orderKey first ≤ orderKey second

end TileChunk

/-- 1つの待ち牌と、その牌を加えた和了形の1つの分割。 -/
structure WaitCompletion where
  wait : Tile
  winningChunks : List TileChunk
deriving BEq, DecidableEq, Repr
