import Mahjong.Basic

/-!
# 牌パターン

このモジュールでは、待ち分類を構成する小さな部品を定義する。
`Taats`、`Toitsu`、`Tanki`、`Shuntsu`、`MentsuCandidate` はいずれも
`HasTilePattern` インスタンスを持ち、必要な牌種列を共通の方法で取り出せる。
-/

/--
ターツ。常に同じスートの数牌2枚で構成する。

ランクは0始まりで扱う。`ryanmen` は実際の2--7始まり、`kanchan` は1--7始まり、
`penchan` は1--2または8--9を表す。
-/
inductive Taats
| ryanmen (suit : Suit) (start : Fin 6)
| kanchan (suit : Suit) (start : Fin 7)
| penchan (suit : Suit) (high : Bool)
deriving BEq, DecidableEq, Repr, Fintype

namespace Taats

/-- ターツを構成する2枚の牌種列。 -/
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

/-- 対子。同じ牌種2枚からなる。 -/
inductive Toitsu
| toitsu  (t: Tile)
deriving BEq, DecidableEq, Repr, Fintype

namespace Toitsu

/-- 対子を構成する2枚の牌種列。 -/
def tiles : Toitsu → List Tile
  | .toitsu tile => pairTiles tile

instance : HasTilePattern Toitsu where
  tiles := Toitsu.tiles

noncomputable def take (toitsu : Toitsu) (chunk : Chunk) :
    Option (List PhysicalTile × Finset PhysicalTile) :=
  HasTilePattern.take toitsu chunk

end Toitsu

/-- 単騎待ちの核になる1枚の牌種。 -/
inductive Tanki
| tanki (t : Tile)
deriving BEq, DecidableEq, Repr, Fintype

namespace Tanki

/-- 単騎を構成する1枚の牌種列。 -/
def tiles : Tanki → List Tile
  | .tanki tile => [tile]

instance : HasTilePattern Tanki where
  tiles := Tanki.tiles

noncomputable def all : List Tanki :=
  (Finset.univ : Finset Tanki).toList

/-- 物理牌がこの単騎の牌種と一致すること。 -/
def Matches (tanki : Tanki) (tile : PhysicalTile) : Prop :=
  tanki.tiles = [tile.1]

noncomputable def take (tanki : Tanki) (chunk : Chunk) :
    Option (List PhysicalTile × Finset PhysicalTile) :=
  HasTilePattern.take tanki chunk

end Tanki

/-!
## 順子
-/
/-- 順子。数牌の同一スートで、連続する3ランクからなる。 -/
inductive Shuntsu
| shuntsu (suit : Suit) (start : Fin 7)
deriving BEq, DecidableEq, Repr, Fintype

namespace Shuntsu

/-- 順子を構成する3枚の牌種列。 -/
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
/-- 通常形で完成面子として扱う候補。順子または刻子。 -/
inductive MentsuCandidate
| shuntsu (shuntsu : Shuntsu)
| koutsu (t: Tile)
deriving BEq, DecidableEq, Repr, Fintype

namespace MentsuCandidate

/-- 有限型として列挙できるすべての完成面子候補。 -/
noncomputable def all : List MentsuCandidate :=
  (Finset.univ : Finset MentsuCandidate).toList

/-- 完成面子候補を構成する3枚の牌種列。 -/
def tiles : MentsuCandidate → List Tile
  | .shuntsu sequence => sequence.tiles
  | .koutsu tile => koutsuTiles tile

instance : HasTilePattern MentsuCandidate where
  tiles := MentsuCandidate.tiles

def IsShuntsu : MentsuCandidate → Prop
  | .shuntsu _ => True
  | _ => False

/-- 字牌を含む完成面子候補は順子ではない。 -/
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
