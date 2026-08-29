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

/-!
## 4枚手牌の待ちの取り方
-/
inductive FourTileExtraction
| tankiShuntsu (tanki : Tanki) (shuntsu : Shuntsu)
| tankiKoutsu (tanki : Tanki) (tile : Tile)
| toitsuRyanmen (toitsu : Toitsu) (suit : Suit) (start : Fin 6)
| toitsuKanchan (toitsu : Toitsu) (suit : Suit) (start : Fin 7)
| toitsuPenchan (toitsu : Toitsu) (suit : Suit) (high : Bool)
| shanpon (first second : Toitsu)
deriving BEq, DecidableEq, Repr, Fintype

namespace FourTileExtraction

noncomputable def all : List FourTileExtraction :=
  (Finset.univ : Finset FourTileExtraction).toList

def tiles : FourTileExtraction → List Tile
  | .tankiShuntsu tanki shuntsu => tanki.tiles ++ shuntsu.tiles
  | .tankiKoutsu tanki tile => tanki.tiles ++ koutsuTiles tile
  | .toitsuRyanmen toitsu suit start => toitsu.tiles ++ (Taats.ryanmen suit start).tiles
  | .toitsuKanchan toitsu suit start => toitsu.tiles ++ (Taats.kanchan suit start).tiles
  | .toitsuPenchan toitsu suit high => toitsu.tiles ++ (Taats.penchan suit high).tiles
  | .shanpon first second => first.tiles ++ second.tiles

instance : HasTilePattern FourTileExtraction where
  tiles := FourTileExtraction.tiles

noncomputable def take (extraction : FourTileExtraction) (chunk : Chunk) :
    Option (List PhysicalTile × Finset PhysicalTile) :=
  HasTilePattern.take extraction chunk

end FourTileExtraction

inductive FourTileWaitKind
| tankiShuntsu
| tankiKoutsu
| toitsuRyanmen
| toitsuKanchan
| toitsuPenchan
| shanpon
| nobetan
| kuttsukiRyanmen
| kuttsukiKanchan
| kuttsukiPenchan
deriving BEq, DecidableEq, Repr, Fintype

namespace FourTileWaitKind

def all : List FourTileWaitKind :=
  [.tankiShuntsu,
   .tankiKoutsu,
   .toitsuRyanmen,
   .toitsuKanchan,
   .toitsuPenchan,
   .shanpon,
   .nobetan,
   .kuttsukiRyanmen,
   .kuttsukiKanchan,
   .kuttsukiPenchan]

theorem exhaustive (kind : FourTileWaitKind) : kind ∈ all := by
  cases kind <;> simp [all]

end FourTileWaitKind

inductive FourTileAmbiguity
| noAmbiguity
| ambiguous
deriving BEq, DecidableEq, Repr, Fintype

inductive FourTileReducibility
| reducible
| irreducible
deriving BEq, DecidableEq, Repr, Fintype

inductive FourTileWait
| noAmbiguityTankiShuntsu (tanki : Tanki) (shuntsu : Shuntsu)
| noAmbiguityTankiKoutsu (tanki : Tanki) (tile : Tile)
| noAmbiguityToitsuRyanmen (toitsu : Toitsu) (suit : Suit) (start : Fin 6)
| noAmbiguityToitsuKanchan (toitsu : Toitsu) (suit : Suit) (start : Fin 7)
| noAmbiguityToitsuPenchan (toitsu : Toitsu) (suit : Suit) (high : Bool)
| noAmbiguityShanpon (first second : Toitsu)
| ambiguousNobetan (firstTanki : Tanki) (firstShuntsu : Shuntsu)
    (secondTanki : Tanki) (secondShuntsu : Shuntsu)
| ambiguousKuttsukiRyanmen (tanki : Tanki) (tile : Tile)
    (toitsu : Toitsu) (suit : Suit) (start : Fin 6)
| ambiguousKuttsukiKanchan (tanki : Tanki) (tile : Tile)
    (toitsu : Toitsu) (suit : Suit) (start : Fin 7)
| ambiguousKuttsukiPenchan (tanki : Tanki) (tile : Tile)
    (toitsu : Toitsu) (suit : Suit) (high : Bool)
deriving BEq, DecidableEq, Repr

namespace FourTileWait

def reducibility : FourTileWait → FourTileReducibility
  | .noAmbiguityTankiShuntsu .. => .reducible
  | .noAmbiguityTankiKoutsu .. => .reducible
  | .noAmbiguityToitsuRyanmen .. => .irreducible
  | .noAmbiguityToitsuKanchan .. => .irreducible
  | .noAmbiguityToitsuPenchan .. => .irreducible
  | .noAmbiguityShanpon .. => .irreducible
  | .ambiguousNobetan .. => .irreducible
  | .ambiguousKuttsukiRyanmen .. => .irreducible
  | .ambiguousKuttsukiKanchan .. => .irreducible
  | .ambiguousKuttsukiPenchan .. => .irreducible

  /-- One concrete mpsz example for every four-tile wait kind. -/
  def examples : List (String × FourTileWait) :=
    [("1235m: tanki 5m", .noAmbiguityTankiShuntsu
      (.tanki (.numbered .Manzu 4)) (.shuntsu .Manzu 0)),
    ("1115m: tanki 5m", .noAmbiguityTankiKoutsu
      (.tanki (.numbered .Manzu 4)) (.numbered .Manzu 0)),
    ("34m55p: ryanmen 2m/5m", .noAmbiguityToitsuRyanmen
      (.toitsu (.numbered .Pinzu 4)) .Manzu 1),
    ("35m55p: kanchan 4m", .noAmbiguityToitsuKanchan
      (.toitsu (.numbered .Pinzu 4)) .Manzu 2),
    ("12m55p: penchan 3m", .noAmbiguityToitsuPenchan
      (.toitsu (.numbered .Pinzu 4)) .Manzu false),
    ("11m22p: shanpon 1m/2p", .noAmbiguityShanpon
      (.toitsu (.numbered .Manzu 0)) (.toitsu (.numbered .Pinzu 1))),
    ("1234m: nobetan 1m/4m", .ambiguousNobetan
      (.tanki (.numbered .Manzu 0)) (.shuntsu .Manzu 1)
      (.tanki (.numbered .Manzu 3)) (.shuntsu .Manzu 0)),
    ("2223m: kuttsuki ryanmen 1m/3m/4m", .ambiguousKuttsukiRyanmen
      (.tanki (.numbered .Manzu 2)) (.numbered .Manzu 1)
      (.toitsu (.numbered .Manzu 1)) .Manzu 0),
    ("1113m: kuttsuki kanchan 2m/3m", .ambiguousKuttsukiKanchan
      (.tanki (.numbered .Manzu 2)) (.numbered .Manzu 0)
      (.toitsu (.numbered .Manzu 0)) .Manzu 0),
    ("1112m: kuttsuki penchan 2m/3m", .ambiguousKuttsukiPenchan
      (.tanki (.numbered .Manzu 1)) (.numbered .Manzu 0)
      (.toitsu (.numbered .Manzu 0)) .Manzu false)]

  def exampleReducibilities : List FourTileReducibility :=
    examples.map fun entry => entry.2.reducibility

  def classifiedExamples : List (FourTileReducibility × String) :=
    examples.map fun entry => (entry.2.reducibility, entry.1)

  example : exampleReducibilities =
     [.reducible, .reducible,
      .irreducible, .irreducible, .irreducible, .irreducible,
      .irreducible, .irreducible, .irreducible, .irreducible] := by
    native_decide

def kind : FourTileWait → FourTileWaitKind
  | .noAmbiguityTankiShuntsu .. => .tankiShuntsu
  | .noAmbiguityTankiKoutsu .. => .tankiKoutsu
  | .noAmbiguityToitsuRyanmen .. => .toitsuRyanmen
  | .noAmbiguityToitsuKanchan .. => .toitsuKanchan
  | .noAmbiguityToitsuPenchan .. => .toitsuPenchan
  | .noAmbiguityShanpon .. => .shanpon
  | .ambiguousNobetan .. => .nobetan
  | .ambiguousKuttsukiRyanmen .. => .kuttsukiRyanmen
  | .ambiguousKuttsukiKanchan .. => .kuttsukiKanchan
  | .ambiguousKuttsukiPenchan .. => .kuttsukiPenchan

def ambiguity : FourTileWait → FourTileAmbiguity
  | .noAmbiguityTankiShuntsu .. => .noAmbiguity
  | .noAmbiguityTankiKoutsu .. => .noAmbiguity
  | .noAmbiguityToitsuRyanmen .. => .noAmbiguity
  | .noAmbiguityToitsuKanchan .. => .noAmbiguity
  | .noAmbiguityToitsuPenchan .. => .noAmbiguity
  | .noAmbiguityShanpon .. => .noAmbiguity
  | .ambiguousNobetan .. => .ambiguous
  | .ambiguousKuttsukiRyanmen .. => .ambiguous
  | .ambiguousKuttsukiKanchan .. => .ambiguous
  | .ambiguousKuttsukiPenchan .. => .ambiguous

def extractions : FourTileWait → List FourTileExtraction
  | .noAmbiguityTankiShuntsu tanki shuntsu =>
      [.tankiShuntsu tanki shuntsu]
  | .noAmbiguityTankiKoutsu tanki tile =>
      [.tankiKoutsu tanki tile]
  | .noAmbiguityToitsuRyanmen toitsu suit start =>
      [.toitsuRyanmen toitsu suit start]
  | .noAmbiguityToitsuKanchan toitsu suit start =>
      [.toitsuKanchan toitsu suit start]
  | .noAmbiguityToitsuPenchan toitsu suit high =>
      [.toitsuPenchan toitsu suit high]
  | .noAmbiguityShanpon first second =>
      [.shanpon first second]
  | .ambiguousNobetan firstTanki firstShuntsu secondTanki secondShuntsu =>
      [.tankiShuntsu firstTanki firstShuntsu,
       .tankiShuntsu secondTanki secondShuntsu]
  | .ambiguousKuttsukiRyanmen tanki tile toitsu suit start =>
      [.tankiKoutsu tanki tile,
       .toitsuRyanmen toitsu suit start]
  | .ambiguousKuttsukiKanchan tanki tile toitsu suit start =>
      [.tankiKoutsu tanki tile,
       .toitsuKanchan toitsu suit start]
  | .ambiguousKuttsukiPenchan tanki tile toitsu suit high =>
      [.tankiKoutsu tanki tile,
       .toitsuPenchan toitsu suit high]

def extractionCount : FourTileWait → Nat
  | wait => wait.extractions.length

theorem extractions_nonempty (wait : FourTileWait) : wait.extractions ≠ [] := by
  cases wait <;> simp [extractions]

theorem noAmbiguity_extractionCount
    (wait : FourTileWait) (h : wait.ambiguity = .noAmbiguity) :
    wait.extractionCount = 1 := by
  cases wait <;> simp [ambiguity] at h <;> simp [extractionCount, extractions]

theorem ambiguous_extractionCount
    (wait : FourTileWait) (h : wait.ambiguity = .ambiguous) :
    wait.extractionCount = 2 := by
  cases wait <;> simp [ambiguity] at h <;> simp [extractionCount, extractions]

theorem exhaustive (wait : FourTileWait) : wait.kind ∈ FourTileWaitKind.all :=
  FourTileWaitKind.exhaustive wait.kind

end FourTileWait

/-!
## 7枚手牌の待ち

7枚の聴牌に1枚加えて通常形（2面子1雀頭）で和了するとき、和了牌を含まない
完成面子を1つ選べる。したがって残る4枚は `FourTileWait` であり、7枚固有の
基本待ちは増えない。
-/
inductive SevenTileWaitKind
| mentsuThen (remaining : FourTileWaitKind)
deriving BEq, DecidableEq, Repr, Fintype

namespace SevenTileWaitKind

def all : List SevenTileWaitKind :=
  FourTileWaitKind.all.map .mentsuThen

theorem exhaustive (kind : SevenTileWaitKind) : kind ∈ all := by
  cases kind with
  | mentsuThen remaining =>
      simp [all, FourTileWaitKind.exhaustive remaining]

theorem number_of_kinds : all.length = 10 := by
  simp [all, FourTileWaitKind.all]

end SevenTileWaitKind

structure SevenTileExtraction where
  mentsu : MentsuCandidate
  remaining : FourTileExtraction
deriving Repr

namespace SevenTileExtraction

def tiles (extraction : SevenTileExtraction) : List Tile :=
  extraction.mentsu.tiles ++ extraction.remaining.tiles

theorem tiles_length (extraction : SevenTileExtraction) :
    extraction.tiles.length = 7 := by
  have taats_tiles_length (taats : Taats) : taats.tiles.length = 2 := by
    cases taats with
    | ryanmen => simp [Taats.tiles]
    | kanchan => simp [Taats.tiles]
    | penchan _ high => cases high <;> simp [Taats.tiles]
  cases extraction with
  | mk mentsu remaining =>
      cases mentsu <;> cases remaining <;>
        simp [tiles, MentsuCandidate.tiles, Shuntsu.tiles, Tanki.tiles,
          Toitsu.tiles, FourTileExtraction.tiles, pairTiles, koutsuTiles,
          numberedRun, taats_tiles_length]

end SevenTileExtraction

inductive SevenTileWait
| mentsuThen (mentsu : MentsuCandidate) (remaining : FourTileWait)
deriving Repr

inductive SevenTileReducibility
| reducible
| irreducible
deriving BEq, DecidableEq, Repr, Fintype

namespace SevenTileReducibility

def ofFour : FourTileReducibility → SevenTileReducibility
  | .reducible => .reducible
  | .irreducible => .irreducible

end SevenTileReducibility

namespace SevenTileWait

def reducibility : SevenTileWait → SevenTileReducibility
  | .mentsuThen _ remaining => .ofFour remaining.reducibility

/-- One concrete mpsz example for every seven-tile wait kind. -/
def examples : List (String × SevenTileWait) :=
  [("123s1235m: tanki 5m", .mentsuThen
      (.shuntsu (Shuntsu.shuntsu Suit.Souzu 0)) (.noAmbiguityTankiShuntsu
        (.tanki (.numbered .Manzu 4)) (.shuntsu .Manzu 0))),
   ("123s1115m: tanki 5m", .mentsuThen
      (.shuntsu (Shuntsu.shuntsu Suit.Souzu 0)) (.noAmbiguityTankiKoutsu
        (.tanki (.numbered .Manzu 4)) (.numbered .Manzu 0))),
   ("123s34m55p: ryanmen 2m/5m", .mentsuThen
      (.shuntsu (Shuntsu.shuntsu Suit.Souzu 0)) (.noAmbiguityToitsuRyanmen
        (.toitsu (.numbered .Pinzu 4)) .Manzu 1)),
   ("123s35m55p: kanchan 4m", .mentsuThen
      (.shuntsu (Shuntsu.shuntsu Suit.Souzu 0)) (.noAmbiguityToitsuKanchan
        (.toitsu (.numbered .Pinzu 4)) .Manzu 2)),
   ("123s12m55p: penchan 3m", .mentsuThen
      (.shuntsu (Shuntsu.shuntsu Suit.Souzu 0)) (.noAmbiguityToitsuPenchan
        (.toitsu (.numbered .Pinzu 4)) .Manzu false)),
   ("123s11m22p: shanpon 1m/2p", .mentsuThen
      (.shuntsu (Shuntsu.shuntsu Suit.Souzu 0)) (.noAmbiguityShanpon
        (.toitsu (.numbered .Manzu 0)) (.toitsu (.numbered .Pinzu 1)))),
   ("123s1234m: nobetan 1m/4m", .mentsuThen
      (.shuntsu (Shuntsu.shuntsu Suit.Souzu 0)) (.ambiguousNobetan
        (.tanki (.numbered .Manzu 0)) (.shuntsu .Manzu 1)
        (.tanki (.numbered .Manzu 3)) (.shuntsu .Manzu 0))),
   ("123s2223m: kuttsuki ryanmen 1m/3m/4m", .mentsuThen
      (.shuntsu (Shuntsu.shuntsu Suit.Souzu 0)) (.ambiguousKuttsukiRyanmen
        (.tanki (.numbered .Manzu 2)) (.numbered .Manzu 1)
        (.toitsu (.numbered .Manzu 1)) .Manzu 0)),
   ("123s1113m: kuttsuki kanchan 2m/3m", .mentsuThen
      (.shuntsu (Shuntsu.shuntsu Suit.Souzu 0)) (.ambiguousKuttsukiKanchan
        (.tanki (.numbered .Manzu 2)) (.numbered .Manzu 0)
        (.toitsu (.numbered .Manzu 0)) .Manzu 0)),
   ("123s1112m: kuttsuki penchan 2m/3m", .mentsuThen
      (.shuntsu (Shuntsu.shuntsu Suit.Souzu 0)) (.ambiguousKuttsukiPenchan
        (.tanki (.numbered .Manzu 1)) (.numbered .Manzu 0)
        (.toitsu (.numbered .Manzu 0)) .Manzu false))]

def exampleReducibilities : List SevenTileReducibility :=
  examples.map fun entry => entry.2.reducibility

def classifiedExamples : List (SevenTileReducibility × String) :=
  examples.map fun entry => (entry.2.reducibility, entry.1)

example : exampleReducibilities =
    [.reducible, .reducible,
     .irreducible, .irreducible, .irreducible, .irreducible,
     .irreducible, .irreducible, .irreducible, .irreducible] := by
  native_decide

def kind : SevenTileWait → SevenTileWaitKind
  | .mentsuThen _ remaining => .mentsuThen remaining.kind

def ambiguity : SevenTileWait → FourTileAmbiguity
  | .mentsuThen _ remaining => remaining.ambiguity

def extractions : SevenTileWait → List SevenTileExtraction
  | .mentsuThen mentsu remaining =>
      remaining.extractions.map fun extraction => ⟨mentsu, extraction⟩

def extractionCount (wait : SevenTileWait) : Nat :=
  wait.extractions.length

theorem noAmbiguity_extractionCount
    (wait : SevenTileWait) (h : wait.ambiguity = .noAmbiguity) :
    wait.extractionCount = 1 := by
  cases wait with
  | mentsuThen mentsu remaining =>
      simpa [ambiguity, extractionCount, extractions] using
        FourTileWait.noAmbiguity_extractionCount remaining h

theorem ambiguous_extractionCount
    (wait : SevenTileWait) (h : wait.ambiguity = .ambiguous) :
    wait.extractionCount = 2 := by
  cases wait with
  | mentsuThen mentsu remaining =>
      simpa [ambiguity, extractionCount, extractions] using
        FourTileWait.ambiguous_extractionCount remaining h

theorem exhaustive (wait : SevenTileWait) : wait.kind ∈ SevenTileWaitKind.all :=
  SevenTileWaitKind.exhaustive wait.kind

theorem is_mentsu_then_four (wait : SevenTileWait) :
    ∃ mentsu remaining, wait = .mentsuThen mentsu remaining := by
  cases wait with
  | mentsuThen mentsu remaining => exact ⟨mentsu, remaining, rfl⟩

end SevenTileWait

/-!
# 手牌
1, 4, 7, 10, 13だけを考えるのでOK.
-/
inductive Hand where
  | thirteen (tiles : Fin 13 ↪ { pt : PhysicalTile // pt ∈ deck })
  | ten (tiles : Fin 10 ↪ { pt : PhysicalTile // pt ∈ deck })
  | seven (tiles : Fin 7 ↪ { pt : PhysicalTile // pt ∈ deck })
  | four (tiles : Fin 4 ↪ { pt : PhysicalTile // pt ∈ deck })
  | one (tiles : Fin 1 ↪ { pt : PhysicalTile // pt ∈ deck })

namespace Hand

noncomputable def toFinset : Hand → Finset PhysicalTile
  | .thirteen tiles => (Finset.univ : Finset (Fin 13)).image fun i => (tiles i).1
  | .ten tiles => (Finset.univ : Finset (Fin 10)).image fun i => (tiles i).1
  | .seven tiles => (Finset.univ : Finset (Fin 7)).image fun i => (tiles i).1
  | .four tiles => (Finset.univ : Finset (Fin 4)).image fun i => (tiles i).1
  | .one tiles => (Finset.univ : Finset (Fin 1)).image fun i => (tiles i).1

end Hand

/-!
## 手牌からの取り方の列挙
-/
inductive HandExtraction
| tanki (tanki : Tanki) (taken : List PhysicalTile)
| four (extraction : FourTileExtraction) (taken : List PhysicalTile)
| mentsuThen (mentsu : MentsuCandidate) (taken : List PhysicalTile)
    (remaining : HandExtraction)
deriving Repr

namespace HandExtraction

private noncomputable def takeExact (tiles : Finset PhysicalTile) (wanted : List Tile) :
    Option (List PhysicalTile) := do
  let (taken, rest) ← Chunk.takeTilesFrom tiles wanted
  if rest = ∅ then
    some taken
  else
    none

private noncomputable def tankiTerminals (tiles : Finset PhysicalTile) : List HandExtraction :=
  Tanki.all.filterMap fun tanki => do
    let taken ← takeExact tiles tanki.tiles
    some (.tanki tanki taken)

private noncomputable def fourTerminals (tiles : Finset PhysicalTile) : List HandExtraction :=
  FourTileExtraction.all.filterMap fun extraction => do
    let taken ← takeExact tiles extraction.tiles
    some (.four extraction taken)

noncomputable def fromTiles : Nat → Finset PhysicalTile → List HandExtraction
  | 0, tiles => tankiTerminals tiles ++ fourTerminals tiles
  | Nat.succ fuel, tiles =>
      tankiTerminals tiles ++
      fourTerminals tiles ++
      List.flatten (MentsuCandidate.all.map fun mentsu =>
        match Chunk.takeTilesFrom tiles mentsu.tiles with
        | some (taken, rest) =>
            (fromTiles fuel rest).map fun remaining =>
              .mentsuThen mentsu taken remaining
        | none => [])

end HandExtraction

namespace Hand

noncomputable def extractions (hand : Hand) : List HandExtraction :=
  HandExtraction.fromTiles 4 hand.toFinset

end Hand

/-!
## 通常形の待ち分析

`waitingTiles` は実際の待ち牌を返す。`analyzeWait` は、待ち牌を加えた
和了形をチャンクへ分解して得られる集合に対して正規化を行う。
-/
namespace StandardWait

def suits : List Suit := [.Manzu, .Pinzu, .Souzu]

def honors : List Honor :=
  [.East, .South, .West, .North, .White, .Green, .Red]

def numberedTiles : List Tile :=
  suits.flatMap fun suit => List.ofFn fun rank : Fin 9 =>
    Tile.numbered suit rank

def allTiles : List Tile :=
  numberedTiles ++ honors.map .honor

def removeTiles : List Tile → List Tile → Option (List Tile)
  | available, [] => some available
  | available, wanted :: rest =>
      if available.contains wanted then
        removeTiles (available.erase wanted) rest
      else
        none

def meldCandidates : List (List Tile) :=
  (suits.flatMap fun suit =>
    List.ofFn fun start : Fin 7 =>
      numberedRun suit start) ++
  allTiles.map koutsuTiles

def canFormMelds : Nat → List Tile → Bool
  | 0, tiles => tiles.isEmpty
  | fuel + 1, tiles =>
      tiles.isEmpty || meldCandidates.any fun meld =>
        match removeTiles tiles meld with
        | some remaining => canFormMelds fuel remaining
        | none => false

def isWinning (tiles : List Tile) : Bool :=
  tiles.length % 3 == 2 && allTiles.any fun pair =>
    match removeTiles tiles (pairTiles pair) with
    | some remaining => canFormMelds (remaining.length / 3) remaining
    | none => false

def waitingTiles (tiles : List Tile) : List Tile :=
  allTiles.filter fun candidate =>
    (tiles.count candidate < 4) && isWinning (candidate :: tiles)

inductive TileChunk
| pair (tile : Tile)
| shuntsu (suit : Suit) (start : Fin 7)
| koutsu (tile : Tile)
deriving BEq, DecidableEq, Repr

namespace TileChunk

def tiles : TileChunk → List Tile
  | .pair tile => pairTiles tile
  | .shuntsu suit start => numberedRun suit start
  | .koutsu tile => koutsuTiles tile

private def suitKey : Suit → Nat
  | .Manzu => 0
  | .Pinzu => 1
  | .Souzu => 2

private def honorKey : Honor → Nat
  | .East => 0
  | .South => 1
  | .West => 2
  | .North => 3
  | .White => 4
  | .Green => 5
  | .Red => 6

private def tileKey : Tile → Nat
  | .numbered suit rank => suitKey suit * 9 + rank.val
  | .honor honor => 27 + honorKey honor

private def orderKey : TileChunk → Nat
  | .pair tile => tileKey tile
  | .shuntsu suit start => 34 + suitKey suit * 7 + start.val
  | .koutsu tile => 55 + tileKey tile

def canonicalize (chunks : List TileChunk) : List TileChunk :=
  chunks.mergeSort fun first second => orderKey first ≤ orderKey second

end TileChunk

structure WaitDecomposition where
  wait : Tile
  chunks : List TileChunk
deriving BEq, DecidableEq, Repr

def pairChunkCandidates : List TileChunk :=
  allTiles.map .pair

def meldChunkCandidates : List TileChunk :=
  (suits.flatMap fun suit =>
    List.ofFn fun start : Fin 7 =>
      TileChunk.shuntsu suit start) ++
  allTiles.map .koutsu

def decomposeMelds : Nat → List Tile → List (List TileChunk)
  | 0, tiles =>
      if tiles.isEmpty then [[]] else []
  | fuel + 1, tiles =>
      List.flatten (meldChunkCandidates.map fun meld =>
        match removeTiles tiles meld.tiles with
        | some remaining =>
            (decomposeMelds fuel remaining).map fun chunks => meld :: chunks
        | none => [])

def winningDecompositions (tiles : List Tile) : List (List TileChunk) :=
  List.flatten (pairChunkCandidates.map fun pairChunk =>
    match removeTiles tiles pairChunk.tiles with
    | some remaining =>
        (decomposeMelds (remaining.length / 3) remaining).map fun chunks =>
          pairChunk :: chunks
    | none => [])

def waitDecompositionSet (tiles : List Tile) : List WaitDecomposition :=
  ((waitingTiles tiles).flatMap fun wait =>
    (winningDecompositions (wait :: tiles)).map fun chunks =>
      { wait, chunks := TileChunk.canonicalize chunks }).eraseDups

/-!
## 分解に関する既約性

`decompositionCount` は待ち牌と和了形の組を数える。メンツを1つ除いた
聴牌形が同じ個数の分解を持つなら、その手牌はメンツ除去により可約である。
待ちでない牌列を既約とは扱わない。
-/
def decompositionCount (tiles : List Tile) : Nat :=
  (waitDecompositionSet tiles).length

def IsTenpaiTiles (tiles : List Tile) : Prop :=
  waitingTiles tiles ≠ []

instance decidableIsTenpaiTiles (tiles : List Tile) : Decidable (IsTenpaiTiles tiles) := by
  unfold IsTenpaiTiles
  infer_instance

def mentsuReductions (tiles : List Tile) : List (List Tile) :=
  meldChunkCandidates.filterMap fun mentsu =>
    removeTiles tiles mentsu.tiles

def CanReduceMentsu (tiles : List Tile) : Prop :=
  1 < tiles.length ∧ IsTenpaiTiles tiles ∧
    (mentsuReductions tiles).any (fun remaining =>
      !(waitingTiles remaining).isEmpty &&
        decompositionCount remaining == decompositionCount tiles) = true

instance decidableCanReduceMentsu (tiles : List Tile) : Decidable (CanReduceMentsu tiles) := by
  unfold CanReduceMentsu
  infer_instance

def IsIrreducible (tiles : List Tile) : Prop :=
  tiles.length = 1 ∨
    (IsTenpaiTiles tiles ∧ ¬CanReduceMentsu tiles)

instance decidableIsIrreducible (tiles : List Tile) : Decidable (IsIrreducible tiles) := by
  unfold IsIrreducible
  infer_instance

theorem singleton_irreducible (tile : Tile) : IsIrreducible [tile] := by
  simp [IsIrreducible]

theorem not_irreducible_of_canReduceMentsu (tiles : List Tile)
    (reducible : CanReduceMentsu tiles) : ¬IsIrreducible tiles := by
  rcases reducible with ⟨moreThanOne, tenpai, reduction⟩
  intro irreducible
  rcases irreducible with singleton | ⟨_, notReducible⟩
  · omega
  · exact notReducible ⟨moreThanOne, tenpai, reduction⟩

inductive NormalizedTile
| numbered (suitIndex rank : Nat)
| honor (honor : Honor)
deriving BEq, DecidableEq, Repr

inductive NormalizedChunk
| pair (tile : NormalizedTile)
| shuntsu (suitIndex start : Nat)
| koutsu (tile : NormalizedTile)
deriving BEq, DecidableEq, Repr

structure NormalizedDecomposition where
  wait : NormalizedTile
  chunks : List NormalizedChunk
deriving BEq, DecidableEq, Repr

structure Analysis where
  decompositions : List NormalizedDecomposition
deriving BEq, DecidableEq, Repr

private def ranksIn (suit : Suit) (tiles : List Tile) : List Nat :=
  tiles.filterMap fun
    | .numbered tileSuit rank =>
        if tileSuit == suit then some rank.val else none
    | .honor _ => none

private def chunkTiles (decomposition : WaitDecomposition) : List Tile :=
  decomposition.wait :: decomposition.chunks.flatMap TileChunk.tiles

private def suitHasTiles (tiles : List Tile) (suit : Suit) : Bool :=
  !(ranksIn suit tiles).isEmpty

private def presentSuits (tiles : List Tile) : List Suit :=
  suits.filter (suitHasTiles tiles)

private def suitIndexFrom : List Suit → Suit → Nat
  | [], _ => 0
  | current :: rest, suit =>
      if current == suit then 0 else suitIndexFrom rest suit + 1

private def lowestRank (tiles : List Tile) (suit : Suit) : Nat :=
  match ranksIn suit tiles with
  | [] => 0
  | first :: rest => rest.foldl Nat.min first

private def normalizeTile (tiles : List Tile) (present : List Suit) : Tile → NormalizedTile
  | .honor honor => .honor honor
  | .numbered suit rank =>
      .numbered (suitIndexFrom present suit) (rank.val - lowestRank tiles suit)

private def normalizeChunk (tiles : List Tile) (present : List Suit) : TileChunk → NormalizedChunk
  | .pair tile => .pair (normalizeTile tiles present tile)
  | .shuntsu suit start =>
      .shuntsu (suitIndexFrom present suit) (start.val - lowestRank tiles suit)
  | .koutsu tile => .koutsu (normalizeTile tiles present tile)

def normalizeByTranslation (decomposition : WaitDecomposition) : NormalizedDecomposition :=
  let tiles := chunkTiles decomposition
  let present := presentSuits tiles
  { wait := normalizeTile tiles present decomposition.wait
    chunks := decomposition.chunks.map (normalizeChunk tiles present) }

def analysisWith {α : Type} [DecidableEq α]
    (normalize : WaitDecomposition → α) (tiles : List Tile) : List α :=
  (waitDecompositionSet tiles).map normalize |>.eraseDups

def analyzeWait (tiles : List Tile) : Analysis :=
  { decompositions := analysisWith normalizeByTranslation tiles }

/-!
## 部品種別による商

牌の位置を忘れ、待ち牌を除いた各分解を部品種別の多重集合として扱う。
異なる部品種別に異なる素数を割り当て、その積を代表元とする。
-/
inductive ShapeComponent
| tanki
| toitsu
| ryanmen
| kanchan
| penchan
| shuntsu
| koutsu
deriving BEq, DecidableEq, Repr

namespace ShapeComponent

def prime : ShapeComponent → Nat
  | .tanki => 2
  | .toitsu => 3
  | .ryanmen => 5
  | .kanchan => 7
  | .penchan => 11
  | .shuntsu => 13
  | .koutsu => 17

end ShapeComponent

structure ConcreteShapeComponent where
  kind : ShapeComponent
  tiles : List Tile
deriving BEq, DecidableEq, Repr

structure ConcreteShapeExtraction where
  wait : Tile
  components : List ConcreteShapeComponent
deriving BEq, DecidableEq, Repr

structure AbstractShapeExtraction where
  wait : Tile
  components : List ShapeComponent
deriving BEq, DecidableEq, Repr

structure ShapeCodeEntry where
  wait : Tile
  code : Nat
deriving BEq, DecidableEq, Repr

private def completeComponent (chunk : TileChunk) : ConcreteShapeComponent :=
  { kind := match chunk with
      | .pair _ => .toitsu
      | .shuntsu .. => .shuntsu
      | .koutsu _ => .koutsu
    tiles := chunk.tiles }

private def componentWithoutWait (wait : Tile) (chunk : TileChunk) :
    Option ConcreteShapeComponent :=
  let incompleteTiles := chunk.tiles.erase wait
  let result kind := some { kind, tiles := incompleteTiles }
  match chunk with
  | .pair tile =>
      if tile == wait then result .tanki else none
  | .koutsu tile =>
      if tile == wait then result .toitsu else none
  | .shuntsu suit start =>
      match wait with
      | .honor _ => none
      | .numbered waitSuit rank =>
          if waitSuit != suit then none
          else if rank.val == start.val then
            result (if start.val == 6 then .penchan else .ryanmen)
          else if rank.val == start.val + 1 then
            result .kanchan
          else if rank.val == start.val + 2 then
            result (if start.val == 0 then .penchan else .ryanmen)
          else none

private def componentProduct (components : List ShapeComponent) : Nat :=
  components.foldl (fun product component => product * component.prime) 1

private def shapeComponentKey : ShapeComponent → Nat
  | .tanki => 0
  | .toitsu => 1
  | .ryanmen => 2
  | .kanchan => 3
  | .penchan => 4
  | .shuntsu => 5
  | .koutsu => 6

private def concreteTileKey : Tile → Nat
  | .numbered suit rank =>
      (match suit with | .Manzu => 0 | .Pinzu => 1 | .Souzu => 2) * 9 + rank.val
  | .honor honor => 27 + match honor with
      | .East => 0 | .South => 1 | .West => 2 | .North => 3
      | .White => 4 | .Green => 5 | .Red => 6

private def concreteComponentKey (component : ConcreteShapeComponent) : Nat :=
  shapeComponentKey component.kind * 50000 +
    component.tiles.foldl (fun key tile => key * 35 + concreteTileKey tile + 1) 0

private def canonicalizeShapeExtraction
    (components : List ConcreteShapeComponent) : List ConcreteShapeComponent :=
  components.mergeSort fun first second =>
    concreteComponentKey first ≤ concreteComponentKey second

private def concreteShapeExtractionKey (extraction : ConcreteShapeExtraction) : Nat :=
  concreteTileKey extraction.wait * 100000000 +
    extraction.components.foldl (fun key component => key * 500000 + concreteComponentKey component) 0

private def abstractShapeExtractionKey (extraction : AbstractShapeExtraction) : Nat :=
  extraction.components.foldl (fun key component => key * 10 + shapeComponentKey component + 1) 0 * 100 +
    concreteTileKey extraction.wait

private def shapeCodeEntryKey (entry : ShapeCodeEntry) : Nat :=
  entry.code * 100 + concreteTileKey entry.wait

private def decompositionShapeExtractions (decomposition : WaitDecomposition) :
    List (List ConcreteShapeComponent) :=
  let rec selectCompletedChunk : List TileChunk → List (List ConcreteShapeComponent)
    | [] => []
    | chunk :: rest =>
        let later := (selectCompletedChunk rest).map fun extraction =>
          completeComponent chunk :: extraction
        match componentWithoutWait decomposition.wait chunk with
        | some incomplete =>
            (incomplete :: rest.map completeComponent) :: later
        | none => later
  selectCompletedChunk decomposition.chunks

def concreteShapeExtractions (tiles : List Tile) : List ConcreteShapeExtraction :=
  let entries := (waitDecompositionSet tiles).flatMap fun decomposition =>
      (decompositionShapeExtractions decomposition).map fun extraction =>
        { wait := decomposition.wait
          components := canonicalizeShapeExtraction extraction }
  entries
    |>.eraseDups
    |>.mergeSort fun first second =>
      concreteShapeExtractionKey first ≤ concreteShapeExtractionKey second

def abstractShapeExtractions (tiles : List Tile) : List AbstractShapeExtraction :=
  concreteShapeExtractions tiles
    |>.map (fun extraction =>
      { wait := extraction.wait
        components := extraction.components.map (fun component => component.kind) })
    |>.eraseDups
    |>.mergeSort fun first second =>
      abstractShapeExtractionKey first ≤ abstractShapeExtractionKey second

def shapeCodeEntries (tiles : List Tile) : List ShapeCodeEntry :=
  abstractShapeExtractions tiles
    |>.map (fun extraction =>
      { wait := extraction.wait
        code := componentProduct extraction.components })
    |>.eraseDups
    |>.mergeSort fun first second =>
      shapeCodeEntryKey first ≤ shapeCodeEntryKey second

def abstractShapeCodeWithWait (tiles : List Tile) : List (Nat × Tile) :=
  shapeCodeEntries tiles
    |>.map fun entry => (entry.code, entry.wait)

def abstractShapeCode (tiles : List Tile) : List Nat :=
  shapeCodeEntries tiles
    |>.map (fun entry => entry.code)
    |>.eraseDups
    |>.mergeSort (· ≤ ·)

private def manzu (ranks : List Rank) : List Tile :=
  ranks.map (.numbered .Manzu)

private def souzu (ranks : List Rank) : List Tile :=
  ranks.map (.numbered .Souzu)

-- Rank は 0 始まりなので、牌姿の数字から 1 を引いて記述する。
def testHandA : List Tile := manzu [2, 3, 4, 4, 4] ++ souzu [7, 7]
def testHandB : List Tile := manzu [1, 1, 2, 2, 3, 3, 4, 4, 5, 5]
def testHandC : List Tile := souzu [2, 2, 3, 3, 4, 4, 5, 5, 6, 6]
def testHandD : List Tile := manzu [1, 1, 2, 2, 3, 3, 4, 4] ++ souzu [6, 6]
def testHand3456678 : List Tile := manzu [2, 3, 4, 5, 5, 6, 7]
def testHand2345678 : List Tile := manzu [1, 2, 3, 4, 5, 6, 7]
def testHand3334556 : List Tile := manzu [2, 2, 2, 3, 4, 4, 5]
def testHand3335678 : List Tile := manzu [2, 2, 2, 4, 5, 6, 7]
def testHand3335567 : List Tile := manzu [2, 2, 2, 4, 4, 5, 6]
def testHand3335777 : List Tile := manzu [2, 2, 2, 4, 6, 6, 6]
def testHand1167888 : List Tile := manzu [0, 0, 5, 6, 7, 7, 7]
def testHand1166678 : List Tile := manzu [0, 0, 5, 5, 5, 6, 7]

example : abstractShapeExtractions testHand2345678 =
  [{ wait := .numbered .Manzu 1, components := [.tanki, .shuntsu, .shuntsu] },
   { wait := .numbered .Manzu 4, components := [.tanki, .shuntsu, .shuntsu] },
   { wait := .numbered .Manzu 7, components := [.tanki, .shuntsu, .shuntsu] }] := by
  native_decide

example : shapeCodeEntries testHand2345678 =
  [{ wait := .numbered .Manzu 1, code := 338 },
   { wait := .numbered .Manzu 4, code := 338 },
   { wait := .numbered .Manzu 7, code := 338 }] := by
  native_decide

example : abstractShapeCodeWithWait testHand2345678 =
  [(338, .numbered .Manzu 1),
   (338, .numbered .Manzu 4),
   (338, .numbered .Manzu 7)] := by native_decide
example : abstractShapeCode testHand2345678 = [338] := by native_decide
example : abstractShapeCode testHand1167888 = [117, 255] := by native_decide
example : abstractShapeCode testHand1166678 = [117, 255] := by native_decide
example : abstractShapeCode testHand1167888 = abstractShapeCode testHand1166678 := by
  native_decide

/--
The 53 irreducible seven-tile waits using one numbered suit, normalized so the
lowest rank is 1.  Replacing `m` with `p` or `s`, or translating a pattern
without leaving ranks 1--9, gives equivalent concrete examples.
-/
def irreducibleSingleSuitSevenTileExamples : List (String × List Tile) :=
  [("1345666m", manzu [0, 2, 3, 4, 5, 5, 5]),
   ("1234666m", manzu [0, 1, 2, 3, 5, 5, 5]),
   ("1234567m", manzu [0, 1, 2, 3, 4, 5, 6]),
   ("1234555m", manzu [0, 1, 2, 3, 4, 4, 4]),
   ("1234456m", manzu [0, 1, 2, 3, 3, 4, 5]),
   ("1233334m", manzu [0, 1, 2, 2, 2, 2, 3]),
   ("1223344m", manzu [0, 1, 1, 2, 2, 3, 3]),
   ("1222345m", manzu [0, 1, 1, 1, 2, 3, 4]),
   ("1222333m", manzu [0, 1, 1, 1, 2, 2, 2]),
   ("1222234m", manzu [0, 1, 1, 1, 1, 2, 3]),
   ("1178999m", manzu [0, 0, 6, 7, 8, 8, 8]),
   ("1167888m", manzu [0, 0, 5, 6, 7, 7, 7]),
   ("1166678m", manzu [0, 0, 5, 5, 5, 6, 7]),
   ("1156777m", manzu [0, 0, 4, 5, 6, 6, 6]),
   ("1155567m", manzu [0, 0, 4, 4, 4, 5, 6]),
   ("1145678m", manzu [0, 0, 3, 4, 5, 6, 7]),
   ("1145666m", manzu [0, 0, 3, 4, 5, 5, 5]),
   ("1144456m", manzu [0, 0, 3, 3, 3, 4, 5]),
   ("1134567m", manzu [0, 0, 2, 3, 4, 5, 6]),
   ("1134555m", manzu [0, 0, 2, 3, 4, 4, 4]),
   ("1133345m", manzu [0, 0, 2, 2, 2, 3, 4]),
   ("1123456m", manzu [0, 0, 1, 2, 3, 4, 5]),
   ("1123444m", manzu [0, 0, 1, 2, 3, 3, 3]),
   ("1123344m", manzu [0, 0, 1, 2, 2, 3, 3]),
   ("1123333m", manzu [0, 0, 1, 2, 2, 2, 2]),
   ("1122344m", manzu [0, 0, 1, 1, 2, 3, 3]),
   ("1122334m", manzu [0, 0, 1, 1, 2, 2, 3]),
   ("1122333m", manzu [0, 0, 1, 1, 2, 2, 2]),
   ("1122234m", manzu [0, 0, 1, 1, 1, 2, 3]),
   ("1122233m", manzu [0, 0, 1, 1, 1, 2, 2]),
   ("1122223m", manzu [0, 0, 1, 1, 1, 1, 2]),
   ("1113555m", manzu [0, 0, 0, 2, 4, 4, 4]),
   ("1113456m", manzu [0, 0, 0, 2, 3, 4, 5]),
   ("1113444m", manzu [0, 0, 0, 2, 3, 3, 3]),
   ("1113345m", manzu [0, 0, 0, 2, 2, 3, 4]),
   ("1113333m", manzu [0, 0, 0, 2, 2, 2, 2]),
   ("1112444m", manzu [0, 0, 0, 1, 3, 3, 3]),
   ("1112399m", manzu [0, 0, 0, 1, 2, 8, 8]),
   ("1112388m", manzu [0, 0, 0, 1, 2, 7, 7]),
   ("1112377m", manzu [0, 0, 0, 1, 2, 6, 6]),
   ("1112366m", manzu [0, 0, 0, 1, 2, 5, 5]),
   ("1112355m", manzu [0, 0, 0, 1, 2, 4, 4]),
   ("1112346m", manzu [0, 0, 0, 1, 2, 3, 5]),
   ("1112345m", manzu [0, 0, 0, 1, 2, 3, 4]),
   ("1112344m", manzu [0, 0, 0, 1, 2, 3, 3]),
   ("1112334m", manzu [0, 0, 0, 1, 2, 2, 3]),
   ("1112333m", manzu [0, 0, 0, 1, 2, 2, 2]),
   ("1112234m", manzu [0, 0, 0, 1, 1, 2, 3]),
   ("1112233m", manzu [0, 0, 0, 1, 1, 2, 2]),
   ("1112223m", manzu [0, 0, 0, 1, 1, 1, 2]),
   ("1112222m", manzu [0, 0, 0, 1, 1, 1, 1]),
   ("1111333m", manzu [0, 0, 0, 0, 2, 2, 2]),
   ("1111222m", manzu [0, 0, 0, 0, 1, 1, 1])]

example : irreducibleSingleSuitSevenTileExamples.length = 53 := by native_decide

example : irreducibleSingleSuitSevenTileExamples.all
    (fun entry => decide (IsIrreducible entry.2)) = true := by
  native_decide

private def insertAbstractShapeClass (entry : String × List Nat) :
  List (List Nat × List String) → List (List Nat × List String)
  | [] => [(entry.2, [entry.1])]
  | current :: rest =>
      if current.1 == entry.2 then
        (current.1, current.2 ++ [entry.1]) :: rest
      else
        current :: insertAbstractShapeClass entry rest

def irreducibleSevenTileAbstractShapeClasses : List (List Nat × List String) :=
  irreducibleSingleSuitSevenTileExamples.foldl (fun classes entry =>
    insertAbstractShapeClass (entry.1, abstractShapeCode entry.2) classes) []

example : irreducibleSevenTileAbstractShapeClasses.length = 26 := by native_decide

example : irreducibleSevenTileAbstractShapeClasses.find? (fun entry =>
    entry.1 == [117, 255]) = some
      ([117, 255],
       ["1178999m", "1167888m", "1166678m", "1156777m", "1155567m",
        "1145666m", "1144456m", "1134555m", "1133345m", "1122234m",
        "1112399m", "1112388m", "1112377m", "1112366m", "1112355m"]) := by
  native_decide

private def manzuPair (rank : Rank) : TileChunk :=
  .pair (.numbered .Manzu rank)

private def manzuShuntsu (start : Fin 7) : TileChunk :=
  .shuntsu .Manzu start

private def manzuKoutsu (rank : Rank) : TileChunk :=
  .koutsu (.numbered .Manzu rank)

private def manzuDecomposition (wait : Rank) (chunks : List TileChunk) : WaitDecomposition :=
  { wait := .numbered .Manzu wait, chunks }

example : waitingTiles testHandA =
  manzu [1, 4] ++ souzu [7] := by native_decide

example : waitingTiles testHandB = manzu [1, 2, 4, 5] := by native_decide

example : waitingTiles testHandC = souzu [2, 3, 5, 6] := by native_decide

example : waitingTiles testHandD = manzu [1, 4] ++ souzu [6] := by native_decide

example : analyzeWait testHandB = analyzeWait testHandC := by native_decide
example : analyzeWait testHandB ≠ analyzeWait testHandD := by native_decide
example : analyzeWait testHandC ≠ analyzeWait testHandD := by native_decide

-- 3456678: 単騎 3・6、両面 6・9
example : waitDecompositionSet testHand3456678 =
  [manzuDecomposition 2 [manzuPair 2, manzuShuntsu 3, manzuShuntsu 5],
   manzuDecomposition 5 [manzuPair 5, manzuShuntsu 2, manzuShuntsu 5],
   manzuDecomposition 8 [manzuPair 5, manzuShuntsu 2, manzuShuntsu 6]] ∧
  (waitDecompositionSet testHand3456678).length = 3 := by native_decide

-- 2345678: 単騎 2・5・8
example : waitDecompositionSet testHand2345678 =
  [manzuDecomposition 1 [manzuPair 1, manzuShuntsu 2, manzuShuntsu 5],
   manzuDecomposition 4 [manzuPair 4, manzuShuntsu 1, manzuShuntsu 5],
   manzuDecomposition 7 [manzuPair 7, manzuShuntsu 1, manzuShuntsu 4]] ∧
  (waitDecompositionSet testHand2345678).length = 3 := by native_decide

-- 3334556: 単騎 5、嵌張 5、両面 4・7
example : waitDecompositionSet testHand3334556 =
  [manzuDecomposition 3 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 3],
   manzuDecomposition 4 [manzuPair 4, manzuShuntsu 3, manzuKoutsu 2],
   manzuDecomposition 6 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 4]] ∧
  (waitDecompositionSet testHand3334556).length = 3 := by native_decide

-- 3335678: 単騎 5・8、嵌張 4
example : waitDecompositionSet testHand3335678 =
  [manzuDecomposition 3 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 5],
   manzuDecomposition 4 [manzuPair 4, manzuShuntsu 5, manzuKoutsu 2],
   manzuDecomposition 7 [manzuPair 7, manzuShuntsu 4, manzuKoutsu 2]] ∧
  (waitDecompositionSet testHand3335678).length = 3 := by native_decide

-- 3335567: 単騎 5、嵌張 4、両面 5・8
example : waitDecompositionSet testHand3335567 =
  [manzuDecomposition 3 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 4],
   manzuDecomposition 4 [manzuPair 4, manzuShuntsu 4, manzuKoutsu 2],
   manzuDecomposition 7 [manzuPair 4, manzuShuntsu 5, manzuKoutsu 2]] ∧
  (waitDecompositionSet testHand3335567).length = 3 := by native_decide

-- 3335777: 単騎 5、嵌張 4・6
example : waitDecompositionSet testHand3335777 =
  [manzuDecomposition 3 [manzuPair 2, manzuShuntsu 2, manzuKoutsu 6],
   manzuDecomposition 4 [manzuPair 4, manzuKoutsu 2, manzuKoutsu 6],
   manzuDecomposition 5 [manzuPair 6, manzuShuntsu 4, manzuKoutsu 2]] ∧
  (waitDecompositionSet testHand3335777).length = 3 := by native_decide

end StandardWait

/-! # 待ち -/
/-! ## 待ち要素の定義 -/
/-! ### Hand one に対しては単騎のみ -/

inductive Tenpai : Hand → Type
  | tanki
      (tiles : Fin 1 ↪ { pt : PhysicalTile // pt ∈ deck })
      (wait : Tanki)
      (lastTileMatches : wait.Matches (tiles 0).1) :
      Tenpai (.one tiles)
  | four
      (tiles : Fin 4 ↪ { pt : PhysicalTile // pt ∈ deck })
      (wait : FourTileWait) :
      Tenpai (.four tiles)
    | seven
      (tiles : Fin 7 ↪ { pt : PhysicalTile // pt ∈ deck })
      (wait : SevenTileWait) :
      Tenpai (.seven tiles)

def one_is_tenpai (tiles : Fin 1 ↪ { pt : PhysicalTile // pt ∈ deck }) :
    Tenpai (.one tiles) :=
  .tanki tiles (.tanki ((tiles 0).1).1) (by simp [Tanki.Matches, Tanki.tiles])

/-! ## 複合待ちの定義 -/
