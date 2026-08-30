import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-! This is a module for the Lean 4 study project. -/

/-! このプロジェクトのゴール：麻雀の待ちの分類を行うツール提供する。ツールは証明を伴い正しさを保証する。 -/

/-!
 # 麻雀牌の定義
 -/


/-!
 ## 数牌の定義
 -/
 abbrev Rank := Fin 9

 instance (n : Nat) [ofNat : OfNat (Fin 9) n] : OfNat Rank n where
   ofNat := (OfNat.ofNat n : Fin 9)

 inductive Suit
 | Manzu
 | Pinzu
 | Souzu
deriving BEq, DecidableEq, Repr, Fintype


/-!
 ## 字牌の定義
 -/
 inductive Honor
 | East
 | South
 | West
 | North
 | White
 | Green
 | Red
deriving BEq, DecidableEq, Repr, Fintype

/-!
 ## 麻雀牌の種類の定義 -> 萬子・筒子・索子と字牌
 -/
 inductive Tile
 | numbered(suit : Suit) (rank : Rank )
 | honor(h : Honor )
deriving BEq, DecidableEq, Repr, Fintype

/-!
 ## セットの定義
-/
def tileTypes : Finset Tile :=
  Finset.univ

abbrev PhysicalTile := Tile × Fin 4

def deck : Finset PhysicalTile :=
  Finset.univ

theorem deck_cardinality : deck.card = 136 := by
  simp [deck]
  rfl

structure Chunk where
  tiles : Finset PhysicalTile
  nonempty : tiles.Nonempty

namespace Chunk

def take (chunk : Chunk) (tile : { pt : PhysicalTile // pt ∈ chunk.tiles }) :
    PhysicalTile × Finset PhysicalTile :=
  (tile, chunk.tiles.erase tile)

@[simp]
theorem take_fst (chunk : Chunk) (tile : { pt : PhysicalTile // pt ∈ chunk.tiles }) :
    (chunk.take tile).1 = tile := rfl

@[simp]
theorem take_snd_not_mem (chunk : Chunk) (tile : { pt : PhysicalTile // pt ∈ chunk.tiles }) :
    tile.1 ∉ (chunk.take tile).2 := by
  simp [take]

noncomputable def takeTileFrom (tiles : Finset PhysicalTile) (wanted : Tile) :
    Option (PhysicalTile × Finset PhysicalTile) :=
  match tiles.toList.find? (fun tile => tile.1 == wanted) with
  | some tile => some (tile, tiles.erase tile)
  | none => none

noncomputable def takeTilesFrom :
    Finset PhysicalTile → List Tile → Option (List PhysicalTile × Finset PhysicalTile)
  | tiles, [] => some ([], tiles)
  | tiles, wanted :: wantedTiles => do
      let (tile, remaining) ← takeTileFrom tiles wanted
      let (taken, rest) ← takeTilesFrom remaining wantedTiles
      pure (tile :: taken, rest)

noncomputable def takeTiles (chunk : Chunk) (wanted : List Tile) :
    Option (List PhysicalTile × Finset PhysicalTile) :=
  takeTilesFrom chunk.tiles wanted

end Chunk

class HasTilePattern (α : Type) where
  tiles : α → List Tile

namespace HasTilePattern

noncomputable def take {α : Type} [HasTilePattern α] (pattern : α) (chunk : Chunk) :
    Option (List PhysicalTile × Finset PhysicalTile) :=
  chunk.takeTiles (HasTilePattern.tiles pattern)

end HasTilePattern

/-!
 # 麻雀牌の表記
 a) unicode で表す
 b) mpsz
 -/

inductive TileFormat
| unicode
| mpsz
deriving BEq, DecidableEq, Repr

namespace Tile

private def mpszSuffix : Suit → String
| .Manzu => "m"
| .Pinzu => "p"
| .Souzu => "s"

private def honorMpszRank : Honor → Nat
| .East => 1
| .South => 2
| .West => 3
| .North => 4
| .White => 5
| .Green => 6
| .Red => 7

private def numberedUnicodeOffset : Suit → Nat
| .Manzu => 0x1F007
| .Pinzu => 0x1F019
| .Souzu => 0x1F010

private def Honor.unicode : Honor → String
| .East => "🀀"
| .South => "🀁"
| .West => "🀂"
| .North => "🀃"
| .White => "🀆"
| .Green => "🀅"
| .Red => "🀄"

def format (output : TileFormat) : Tile → String
| .numbered suit rank =>
  match output with
  | .unicode => String.singleton (Char.ofNat (numberedUnicodeOffset suit + rank.val))
  | .mpsz => s!"{rank.val + 1}{mpszSuffix suit}"
| .honor h =>
  match output with
  | .unicode => Honor.unicode h
  | .mpsz => s!"{honorMpszRank h}z"

example : format .unicode (.numbered .Manzu 0) = "🀇" := rfl
example : format .mpsz (.numbered .Pinzu 8) = "9p" := rfl
example : format .unicode (.honor .Red) = "🀄" := rfl
example : format .mpsz (.honor .White) = "5z" := rfl

end Tile

/-!
# 牌パターンの共通部品
-/

def pairTiles (tile : Tile) : List Tile :=
  [tile, tile]

def koutsuTiles (tile : Tile) : List Tile :=
  [tile, tile, tile]

def numberedRun (suit : Suit) (start : Fin 7) : List Tile :=
  [Tile.numbered suit ⟨start.val, Nat.lt_trans start.isLt (by decide)⟩,
   Tile.numbered suit ⟨start.val + 1,
    Nat.lt_trans (Nat.add_lt_add_right start.isLt 1) (by decide)⟩,
   Tile.numbered suit ⟨start.val + 2, by
     simpa using Nat.add_lt_add_right start.isLt 2⟩]

