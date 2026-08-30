import Mahjong.FourTileWait

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

abbrev SevenTileReducibility := FourTileReducibility

namespace SevenTileReducibility

def ofFour (reducibility : FourTileReducibility) : SevenTileReducibility :=
  reducibility

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
