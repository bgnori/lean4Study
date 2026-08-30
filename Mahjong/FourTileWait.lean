import Mahjong.Pattern

/-!
# 4枚手牌の待ち分類

4枚手牌は、和了牌を1枚加えると「1面子1雀頭」になる最小の待ち解析単位である。
このモジュールでは、4枚手牌をどの未完成部品として読むかを `FourTileExtraction`、
麻雀上の待ち種別を `FourTileWaitKind`、分類結果を `FourTileWait` として表す。
-/
/-- 4枚の牌を、単騎+面子または対子+ターツとして取り出す方法。 -/
inductive FourTileExtraction
| tankiShuntsu (tanki : Tanki) (shuntsu : Shuntsu)
| tankiKoutsu (tanki : Tanki) (tile : Tile)
| toitsuRyanmen (toitsu : Toitsu) (suit : Suit) (start : Fin 6)
| toitsuKanchan (toitsu : Toitsu) (suit : Suit) (start : Fin 7)
| toitsuPenchan (toitsu : Toitsu) (suit : Suit) (high : Bool)
| shanpon (first second : Toitsu)
deriving BEq, DecidableEq, Repr, Fintype

namespace FourTileExtraction

/-- 有限型として列挙できるすべての4枚抽出候補。 -/
noncomputable def all : List FourTileExtraction :=
  (Finset.univ : Finset FourTileExtraction).toList

/-- 抽出候補が要求する4枚の牌種列。 -/
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

/-- 4枚手牌で現れる待ちの種類。 -/
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

/-- `FourTileWaitKind` の明示的な列挙。ドキュメント上の分類表としても使う。 -/
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

/-- 分解が一意か、複数の読みを持つか。 -/
inductive FourTileAmbiguity
| noAmbiguity
| ambiguous
deriving BEq, DecidableEq, Repr, Fintype

/-- 完成面子を取り除いてより小さい待ちへ還元できるか。 -/
inductive FourTileReducibility
| reducible
| irreducible
deriving BEq, DecidableEq, Repr, Fintype

/-- 4枚待ちの分類ラベル。種類、曖昧性、既約性をまとめる。 -/
structure FourTileClassification where
  kind : FourTileWaitKind
  ambiguity : FourTileAmbiguity
  reducibility : FourTileReducibility
deriving BEq, DecidableEq, Repr

/--
4枚待ちの具体的な証拠。

曖昧でない待ちは1つの抽出を持つ。`ambiguousNobetan` と `ambiguousKuttsuki*` は、
同じ4枚手牌が2通りの自然な抽出を持つことを明示的に保持する。
-/
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

/-- `FourTileWait` の各コンストラクタに対応する分類ラベル。 -/
def classification : FourTileWait → FourTileClassification
  | .noAmbiguityTankiShuntsu .. =>
    ⟨.tankiShuntsu, .noAmbiguity, .reducible⟩
  | .noAmbiguityTankiKoutsu .. =>
    ⟨.tankiKoutsu, .noAmbiguity, .reducible⟩
  | .noAmbiguityToitsuRyanmen .. =>
    ⟨.toitsuRyanmen, .noAmbiguity, .irreducible⟩
  | .noAmbiguityToitsuKanchan .. =>
    ⟨.toitsuKanchan, .noAmbiguity, .irreducible⟩
  | .noAmbiguityToitsuPenchan .. =>
    ⟨.toitsuPenchan, .noAmbiguity, .irreducible⟩
  | .noAmbiguityShanpon .. =>
    ⟨.shanpon, .noAmbiguity, .irreducible⟩
  | .ambiguousNobetan .. =>
    ⟨.nobetan, .ambiguous, .irreducible⟩
  | .ambiguousKuttsukiRyanmen .. =>
    ⟨.kuttsukiRyanmen, .ambiguous, .irreducible⟩
  | .ambiguousKuttsukiKanchan .. =>
    ⟨.kuttsukiKanchan, .ambiguous, .irreducible⟩
  | .ambiguousKuttsukiPenchan .. =>
    ⟨.kuttsukiPenchan, .ambiguous, .irreducible⟩

/-- この4枚待ちが面子除去で還元可能かどうか。 -/
def reducibility (wait : FourTileWait) : FourTileReducibility :=
  wait.classification.reducibility

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

/-- この4枚待ちの待ち種別。 -/
def kind (wait : FourTileWait) : FourTileWaitKind :=
  wait.classification.kind

/-- この4枚待ちの分解が一意かどうか。 -/
def ambiguity (wait : FourTileWait) : FourTileAmbiguity :=
  wait.classification.ambiguity

/-- この待ちを説明する4枚抽出の列。曖昧な待ちは2要素になる。 -/
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

/-- どの4枚待ちも、少なくとも1つの抽出を持つ。 -/
theorem extractions_nonempty (wait : FourTileWait) : wait.extractions ≠ [] := by
  cases wait <;> simp [extractions]

theorem noAmbiguity_extractionCount
    (wait : FourTileWait) (h : wait.ambiguity = .noAmbiguity) :
    wait.extractionCount = 1 := by
  cases wait <;> simp [ambiguity, classification] at h <;>
    simp [extractionCount, extractions]

theorem ambiguous_extractionCount
    (wait : FourTileWait) (h : wait.ambiguity = .ambiguous) :
    wait.extractionCount = 2 := by
  cases wait <;> simp [ambiguity, classification] at h <;>
    simp [extractionCount, extractions]

theorem exhaustive (wait : FourTileWait) : wait.kind ∈ FourTileWaitKind.all :=
  FourTileWaitKind.exhaustive wait.kind

end FourTileWait
