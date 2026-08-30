import Mahjong.Basic

/-!
# ターツ・メンツの定義
-/
/-!
## ターツの定義
-/
/-! A taatsu is always made of two suited tiles of the same suit.
  Ranks are zero-based: `ryanmen` starts at 2--7, `kanchan` at 1--7,
  and `penchan` represents 1--2 or 8--9. -/
inductive Taats
| ryanmen (suit : Suit) (start : Fin 6)
| kanchan (suit : Suit) (start : Fin 7)
| penchan (suit : Suit) (high : Bool)
deriving BEq, DecidableEq, Repr, Fintype

namespace Taats

def tiles : Taats → List Tile
  | .ryanmen suit start =>
      [.numbered suit ⟨start.val + 1,
        Nat.lt_trans (Nat.add_lt_add_right start.isLt 1) (by decide)⟩,
       .numbered suit ⟨start.val + 2,
        Nat.lt_trans (Nat.add_lt_add_right start.isLt 2) (by decide)⟩]
  | .kanchan suit start =>
      [.numbered suit ⟨start.val, Nat.lt_trans start.isLt (by decide)⟩,
       .numbered suit ⟨start.val + 2, by
         simpa using Nat.add_lt_add_right start.isLt 2⟩]
  | .penchan suit false => [.numbered suit 0, .numbered suit 1]
  | .penchan suit true => [.numbered suit 7, .numbered suit 8]

instance : HasTilePattern Taats where
  tiles := Taats.tiles

noncomputable def take (taats : Taats) (chunk : Chunk) :
    Option (List PhysicalTile × Finset PhysicalTile) :=
  HasTilePattern.take taats chunk

end Taats

inductive Toitsu
| toitsu  (t: Tile)
deriving BEq, DecidableEq, Repr, Fintype

namespace Toitsu

def tiles : Toitsu → List Tile
  | .toitsu tile => pairTiles tile

instance : HasTilePattern Toitsu where
  tiles := Toitsu.tiles

noncomputable def take (toitsu : Toitsu) (chunk : Chunk) :
    Option (List PhysicalTile × Finset PhysicalTile) :=
  HasTilePattern.take toitsu chunk

end Toitsu

inductive Tanki
| tanki (t : Tile)
deriving BEq, DecidableEq, Repr, Fintype

namespace Tanki

def tiles : Tanki → List Tile
  | .tanki tile => [tile]

instance : HasTilePattern Tanki where
  tiles := Tanki.tiles

noncomputable def all : List Tanki :=
  (Finset.univ : Finset Tanki).toList

def Matches (tanki : Tanki) (tile : PhysicalTile) : Prop :=
  tanki.tiles = [tile.1]

noncomputable def take (tanki : Tanki) (chunk : Chunk) :
    Option (List PhysicalTile × Finset PhysicalTile) :=
  HasTilePattern.take tanki chunk

end Tanki

/-!
## 順子
-/
inductive Shuntsu
| shuntsu (suit : Suit) (start : Fin 7)
deriving BEq, DecidableEq, Repr, Fintype

namespace Shuntsu

def tiles : Shuntsu → List Tile
  | .shuntsu suit start => numberedRun suit start

instance : HasTilePattern Shuntsu where
  tiles := Shuntsu.tiles

noncomputable def take (shuntsu : Shuntsu) (chunk : Chunk) :
    Option (List PhysicalTile × Finset PhysicalTile) :=
  HasTilePattern.take shuntsu chunk

end Shuntsu

/-!
## メンツ
-/
inductive MentsuCandidate
| shuntsu (shuntsu : Shuntsu)
| koutsu (t: Tile)
deriving BEq, DecidableEq, Repr, Fintype

namespace MentsuCandidate

noncomputable def all : List MentsuCandidate :=
  (Finset.univ : Finset MentsuCandidate).toList

def tiles : MentsuCandidate → List Tile
  | .shuntsu sequence => sequence.tiles
  | .koutsu tile => koutsuTiles tile

instance : HasTilePattern MentsuCandidate where
  tiles := MentsuCandidate.tiles

def IsShuntsu : MentsuCandidate → Prop
  | .shuntsu _ => True
  | _ => False

theorem honor_not_in_shuntsu (candidate : MentsuCandidate) (honor : Honor)
    (honor_mem : Tile.honor honor ∈ candidate.tiles) : ¬candidate.IsShuntsu := by
  cases candidate with
  | koutsu tile => simp [IsShuntsu]
  | shuntsu sequence =>
      cases sequence
      simp [tiles, Shuntsu.tiles, numberedRun] at honor_mem

noncomputable def take (candidate : MentsuCandidate) (chunk : Chunk) :
    Option (List PhysicalTile × Finset PhysicalTile) :=
  HasTilePattern.take candidate chunk

end MentsuCandidate

