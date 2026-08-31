import Mahjong.Basic
import Mahjong.Pattern

/-!
# 待ちと和了分割

`WaitCompletion` は、1つの待ち牌と、その牌を加えたときの通常形の和了分割を表す。
牌列から `WaitCompletion` を見つける処理は `WaitCompletionFinder`、見つかった形の符号化は
`WaitReadingCode` が担当する。
-/

namespace TileChunk

/-- 完成分割内のチャンクを正規化するための全順序キー。 -/
def orderKey : TileChunk → Nat
  | .inl (.toitsu tile) => tile.orderKey
  | .inr (.shuntsu (.shuntsu suit start)) =>
      Tile.count + suit.orderKey * shuntsuStartCount + start.val
  | .inr (.koutsu tile) => Tile.count + Suit.count * shuntsuStartCount + tile.orderKey

/-- チャンクの正規化キーは異なるチャンクを区別する。 -/
theorem orderKey_injective : Function.Injective orderKey := by
  native_decide

private def orderLE (a b : TileChunk) : Bool :=
  decide (orderKey a ≤ orderKey b)

private theorem orderKeyLE_trans (a b c : TileChunk) :
    orderLE a b = true → orderLE b c = true → orderLE a c = true := by
  simp [orderLE]
  intro first second
  omega

private theorem orderKeyLE_total (a b : TileChunk) :
    (orderLE a b || orderLE b a) = true := by
  simp [orderLE, Nat.le_total]

/-- 分割内の部品順を一意にする。 -/
def canonicalize (winningChunks : List TileChunk) : List TileChunk :=
  winningChunks.mergeSort orderLE

/-- 同じチャンク多重集合は、入力順によらず同じ正規形を持つ。 -/
theorem canonicalize_eq_of_perm {first second : List TileChunk}
    (permutation : first.Perm second) :
    canonicalize first = canonicalize second := by
  apply List.Perm.eq_of_pairwise (le := fun a b => orderKey a ≤ orderKey b)
  · intro a b _ _ firstLe secondLe
    apply orderKey_injective
    omega
  · simpa [canonicalize, orderLE] using
      List.pairwise_mergeSort orderKeyLE_trans orderKeyLE_total first
  · simpa [canonicalize, orderLE] using
      List.pairwise_mergeSort orderKeyLE_trans orderKeyLE_total second
  · exact (List.mergeSort_perm _ _).trans
      (permutation.trans (List.mergeSort_perm _ _).symm)

end TileChunk

/-- 1つの待ち牌と、その牌を加えた和了形の1つの分割。 -/
structure WaitCompletion where
  wait : Tile
  winningChunks : List TileChunk
deriving BEq, DecidableEq, Repr
