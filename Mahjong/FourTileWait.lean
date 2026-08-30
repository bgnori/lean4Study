import Mahjong.Pattern

/-!
# 4枚手牌の待ち分類

4枚手牌は、和了牌を1枚加えると「1面子1雀頭」になる最小の待ち解析単位である。
このモジュールでは、4枚手牌をどの未完成部品として読むかを `FourTileExtraction`、
麻雀上の分類語彙を `FourTileWaitKind` として表す。実際に待ちであることは
`ShapeFinder.IsWaitFor` が定め、分類は解析結果から計算する。
-/
/-- 1面子を含む通常形聴牌の手牌枚数。 -/
abbrev fourTileHandSize : Nat := standardTenpaiHandSize 1

/-- 4枚の牌を、単騎+面子または対子+ターツとして取り出す方法。 -/
inductive FourTileExtraction
| tankiShuntsu (tanki : Tanki) (shuntsu : Shuntsu)
| tankiKoutsu (tanki : Tanki) (tile : Tile)
| toitsuRyanmen (toitsu : Toitsu) (suit : Suit) (start : RyanmenStart)
| toitsuKanchan (toitsu : Toitsu) (suit : Suit) (start : ShuntsuStart)
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
  | .tankiKoutsu tanki tile => tanki.tiles ++ (MentsuCandidate.koutsu tile).tiles
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

/-- 4枚待ちの分類語彙に対応する性質。 -/
def FourTileWaitKind.classification : FourTileWaitKind → FourTileClassification
  | .tankiShuntsu =>
    ⟨.tankiShuntsu, .noAmbiguity, .reducible⟩
  | .tankiKoutsu =>
    ⟨.tankiKoutsu, .noAmbiguity, .reducible⟩
  | .toitsuRyanmen =>
    ⟨.toitsuRyanmen, .noAmbiguity, .irreducible⟩
  | .toitsuKanchan =>
    ⟨.toitsuKanchan, .noAmbiguity, .irreducible⟩
  | .toitsuPenchan =>
    ⟨.toitsuPenchan, .noAmbiguity, .irreducible⟩
  | .shanpon =>
    ⟨.shanpon, .noAmbiguity, .irreducible⟩
  | .nobetan =>
    ⟨.nobetan, .ambiguous, .irreducible⟩
  | .kuttsukiRyanmen =>
    ⟨.kuttsukiRyanmen, .ambiguous, .irreducible⟩
  | .kuttsukiKanchan =>
    ⟨.kuttsukiKanchan, .ambiguous, .irreducible⟩
  | .kuttsukiPenchan =>
    ⟨.kuttsukiPenchan, .ambiguous, .irreducible⟩

/-- この分類の既約性。 -/
def FourTileWaitKind.reducibility (kind : FourTileWaitKind) : FourTileReducibility :=
  kind.classification.reducibility

/-- この分類が複数の自然な読みを持つか。 -/
def FourTileWaitKind.ambiguity (kind : FourTileWaitKind) : FourTileAmbiguity :=
  kind.classification.ambiguity
