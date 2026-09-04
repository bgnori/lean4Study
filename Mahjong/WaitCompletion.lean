import Mahjong.Basic
import Mahjong.Pattern

/-!
# 待ちと和了分割

`WaitCompletion` は、1つの待ち牌と、その牌を加えたときの通常形の和了分割を表す。
牌列から `WaitCompletion` を見つける処理は `WaitCompletionFinder`、見つかった形の符号化は
`WaitReadingCode` が担当する。
-/

namespace TileChunk

/--
完成分割内の部品を正規化するための数値キー。

雀頭、順子、刻子には互いに重ならない数値範囲を割り当てる。それぞれの範囲内では、牌種、
スート、順子の開始位置からキーを決める。後続の `canonicalize` はこのキーの順に完成部品を並べる。
-/
def orderKey : TileChunk → Nat
  | .inl (.toitsu tile) => tile.orderKey
  | .inr (.shuntsu (.shuntsu suit start)) =>
      Tile.count + suit.orderKey * shuntsuStartCount + start.val
  | .inr (.koutsu tile) => Tile.count + Suit.count * shuntsuStartCount + tile.orderKey

example : orderKey (TileChunk.pair (.numbered .Manzu 4)) = 4 := rfl
example : orderKey (TileChunk.shuntsu .Pinzu ⟨3, by decide⟩) = 44 := rfl
example : orderKey (TileChunk.koutsu (.honor .East)) = 82 := rfl

/--
完成部品の正規化キーが等しければ、元の完成部品も等しい。

これは `orderKey` が雀頭、順子、刻子を同じ番号へ潰さず、各種類の内部でも異なる牌や順子を
区別することを保証する。したがって、後続処理は完成部品そのものではなく数値キーを使って整列しても、
部品を見分けるための情報を失わない。

`TileChunk` は有限個しかないため、証明では `native_decide` がすべての組合せを計算してこの主張を確認する。

読むためのLean語彙: `Function.Injective`, `native_decide`。
-/
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
