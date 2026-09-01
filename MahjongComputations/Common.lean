import Mahjong.Basic

/-!
# 麻雀計算モジュールの共通処理
-/

namespace MahjongComputations

/-- 牌種ごとの枚数を、物理上限より1大きい基数で符号化した多重集合キー。 -/
def tileMultisetKey (tiles : List Tile) : Nat :=
  Tile.all.foldl (fun key tile => key * (copiesPerTile + 1) + tiles.count tile) 0

end MahjongComputations
