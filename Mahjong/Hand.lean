import Mahjong.Pattern

/-!
# 手牌

このモジュールでは、物理牌の集合としての手牌と、通常形の意味論が扱う牌種列への
変換を定義する。

通常形では、聴牌時の手牌枚数は `3n + 1` になる。ここでは学習対象として
1枚、4枚、7枚、10枚、13枚の手牌だけを扱う。
-/
/--
解析対象にする手牌。通常手の上限以下の面子数と、その面子数に対応する枚数の物理牌を持つ。
埋め込みにより、同じ物理牌は重複しない。
-/
structure Hand where
  mentsuCount : Fin (standardHandMentsuCount + 1)
  tiles : Fin (standardTenpaiHandSize mentsuCount) ↪ PhysicalTile

namespace Hand

/-- 手牌を通常形の意味論が扱う牌種列へ変換する。 -/
def tileTypes (hand : Hand) : List Tile :=
  List.ofFn fun index => (hand.tiles index).1

end Hand
