import Mahjong.Pattern

/-!
# 手牌

このモジュールでは、物理牌の集合としての手牌と、通常形の意味論が扱う牌種列への
変換を定義する。

通常形では、聴牌時の手牌枚数は `3n + 1` になる。ここでは学習対象として
1枚、4枚、7枚、10枚、13枚の手牌だけを扱う。
-/
/-- 通常形聴牌として扱う最大手牌サイズ。 -/
abbrev thirteenTileHandSize : Nat := standardTenpaiHandSize standardHandMentsuCount

/-- 3面子を除去できる手牌サイズ。 -/
abbrev tenTileHandSize : Nat := thirteenTileHandSize - mentsuTileCount

/-- 2面子を除去できる手牌サイズ。 -/
abbrev sevenTileHandSize : Nat := tenTileHandSize - mentsuTileCount

/-- 1面子を含む通常形聴牌の手牌枚数。 -/
abbrev fourTileHandSize : Nat := standardTenpaiHandSize 1

/-- 単騎だけの最小手牌サイズ。 -/
abbrev oneTileHandSize : Nat := fourTileHandSize - mentsuTileCount

/-- 解析対象にする手牌サイズ。各手牌は `deck` から重複なく取られた物理牌で表す。 -/
inductive Hand where
  | thirteen (tiles : Fin thirteenTileHandSize ↪ { pt : PhysicalTile // pt ∈ deck })
  | ten (tiles : Fin tenTileHandSize ↪ { pt : PhysicalTile // pt ∈ deck })
  | seven (tiles : Fin sevenTileHandSize ↪ { pt : PhysicalTile // pt ∈ deck })
  | four (tiles : Fin fourTileHandSize ↪ { pt : PhysicalTile // pt ∈ deck })
  | one (tiles : Fin oneTileHandSize ↪ { pt : PhysicalTile // pt ∈ deck })

namespace Hand

/-- 手牌を物理牌の有限集合に変換する。 -/
noncomputable def toFinset : Hand → Finset PhysicalTile
  | .thirteen tiles => (Finset.univ : Finset (Fin thirteenTileHandSize)).image fun i => (tiles i).1
  | .ten tiles => (Finset.univ : Finset (Fin tenTileHandSize)).image fun i => (tiles i).1
  | .seven tiles => (Finset.univ : Finset (Fin sevenTileHandSize)).image fun i => (tiles i).1
  | .four tiles => (Finset.univ : Finset (Fin fourTileHandSize)).image fun i => (tiles i).1
  | .one tiles => (Finset.univ : Finset (Fin oneTileHandSize)).image fun i => (tiles i).1

/-- 手牌を通常形の意味論が扱う牌種列へ変換する。 -/
noncomputable def tileTypes (hand : Hand) : List Tile :=
  hand.toFinset.toList.map Prod.fst

end Hand
