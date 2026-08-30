import Mahjong.Basic

/-!
# 牌パターン

このモジュールでは、待ち分類を構成する小さな部品を定義する。
`Taats`、`Toitsu`、`Tanki`、`Shuntsu`、`MentsuCandidate` はいずれも
`HasTilePattern` インスタンスを持ち、必要な牌種列を共通の方法で取り出せる。
完成部品 `TileChunk` は、雀頭 `Toitsu` と面子候補 `MentsuCandidate` の直和として表す。
-/

/-- 完成面子を構成する牌の枚数。 -/
abbrev mentsuTileCount : Nat := 3

/-- 通常の最大手牌に含まれる面子数。 -/
abbrev standardHandMentsuCount : Nat := 4

/-- 通常形に含まれる雀頭の数。 -/
abbrev standardHandPairCount : Nat := 1

/-- 指定した面子数に対応する通常形聴牌の手牌枚数。 -/
def standardTenpaiHandSize (mentsuCount : Nat) : Nat :=
  mentsuCount * mentsuTileCount + standardHandPairCount

/-- 両面ターツの開始位置数。 -/
abbrev ryanmenStartCount : Nat := numberedRankCount - 3

/-- 順子・嵌張ターツの開始位置数。 -/
abbrev shuntsuStartCount : Nat := numberedRankCount - 2

/-- 最初の順子開始位置。 -/
abbrev firstShuntsuStart : Nat := Rank.first.val

/-- 最後の順子開始位置。 -/
abbrev lastShuntsuStart : Nat := shuntsuStartCount - 1

/-- 両面ターツの開始位置。 -/
abbrev RyanmenStart := Fin ryanmenStartCount

/-- 順子・嵌張ターツの開始位置。 -/
abbrev ShuntsuStart := Fin shuntsuStartCount

namespace RyanmenStart

/-- 両面ターツの低い側のランク。 -/
def lowerRank (start : RyanmenStart) : Rank :=
  ⟨start.val + 1, Nat.lt_trans (Nat.add_lt_add_right start.isLt 1) (by decide)⟩

/-- 両面ターツの高い側のランク。 -/
def upperRank (start : RyanmenStart) : Rank :=
  ⟨start.val + 2, Nat.lt_trans (Nat.add_lt_add_right start.isLt 2) (by decide)⟩

end RyanmenStart

namespace ShuntsuStart

/-- 順子の先頭ランク。 -/
def firstRank (start : ShuntsuStart) : Rank :=
  ⟨start.val, Nat.lt_trans start.isLt (by decide)⟩

/-- 順子の中央ランク。 -/
def middleRank (start : ShuntsuStart) : Rank :=
  ⟨start.val + 1, Nat.lt_trans (Nat.add_lt_add_right start.isLt 1) (by decide)⟩

/-- 順子の終端ランク。 -/
def lastRank (start : ShuntsuStart) : Rank :=
  ⟨start.val + 2, Nat.add_lt_add_right start.isLt 2⟩

/-- 最初の順子開始位置かどうか。 -/
def isFirst (start : ShuntsuStart) : Bool :=
  start.val == firstShuntsuStart

/-- 最後の順子開始位置かどうか。 -/
def isLast (start : ShuntsuStart) : Bool :=
  start.val == lastShuntsuStart

end ShuntsuStart

/--
ターツ。常に同じスートの数牌2枚で構成する。

ランクは0始まりで扱う。`ryanmen` は実際の2--7始まり、`kanchan` は1--7始まり、
`penchan` は1--2または8--9を表す。
-/
inductive Taats
| ryanmen (suit : Suit) (start : RyanmenStart)
| kanchan (suit : Suit) (start : ShuntsuStart)
| penchan (suit : Suit) (high : Bool)
deriving BEq, DecidableEq, Repr, Fintype

namespace Taats

/-- ターツを構成する2枚の牌種列。 -/
def tiles : Taats → List Tile
  | .ryanmen suit start =>
      [.numbered suit start.lowerRank,
       .numbered suit start.upperRank]
  | .kanchan suit start =>
      [.numbered suit start.firstRank,
       .numbered suit start.lastRank]
  | .penchan suit false => [.numbered suit Rank.first, .numbered suit Rank.second]
  | .penchan suit true => [.numbered suit Rank.penultimate, .numbered suit Rank.last]

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
  | .toitsu tile => [tile, tile]

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
| shuntsu (suit : Suit) (start : ShuntsuStart)
deriving BEq, DecidableEq, Repr, Fintype

namespace Shuntsu

/-- 順子を構成する3枚の牌種列。 -/
def tiles : Shuntsu → List Tile
  | .shuntsu suit start =>
      [.numbered suit start.firstRank,
       .numbered suit start.middleRank,
       .numbered suit start.lastRank]

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
  | .koutsu tile => [tile, tile, tile]

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
      simp [tiles, Shuntsu.tiles] at honor_mem

noncomputable def take (candidate : MentsuCandidate) (chunk : Chunk) :
    Option (List PhysicalTile × Finset PhysicalTile) :=
  HasTilePattern.take candidate chunk

end MentsuCandidate

/-- 通常形の和了分割に現れる完成部品。雀頭または完成面子。 -/
abbrev TileChunk := Toitsu ⊕ MentsuCandidate

namespace TileChunk

/-- 指定した牌種の雀頭を完成部品として作る。 -/
def pair (tile : Tile) : TileChunk :=
  .inl (.toitsu tile)

/-- 指定した順子を完成部品として作る。 -/
def shuntsu (suit : Suit) (start : ShuntsuStart) : TileChunk :=
  .inr (.shuntsu (.shuntsu suit start))

/-- 指定した牌種の刻子を完成部品として作る。 -/
def koutsu (tile : Tile) : TileChunk :=
  .inr (.koutsu tile)

/-- 完成部品を構成する牌種列。 -/
def tiles : TileChunk → List Tile
  | .inl pair => pair.tiles
  | .inr mentsu => mentsu.tiles

instance : HasTilePattern TileChunk where
  tiles := TileChunk.tiles

end TileChunk
