import Mahjong.Pattern

/-!
# 通常形聴牌の待ち分類

このモジュールでは、通常形聴牌をどの未完成部品として読むかを `WaitExtraction`、
麻雀上の分類語彙を `WaitKind` として表す。実際に待ちであることは
`DecompositionFinder.IsWaitFor` が定め、分類は `Decomposition` の解析結果から計算する。
-/

/-- 待ちの終端を、単騎+面子または対子+ターツとして取り出す方法。 -/
inductive WaitExtraction
| tankiShuntsu (tanki : Tanki) (shuntsu : Shuntsu)
| tankiKoutsu (tanki : Tanki) (tile : Tile)
| toitsuRyanmen (toitsu : Toitsu) (suit : Suit) (start : RyanmenStart)
| toitsuKanchan (toitsu : Toitsu) (suit : Suit) (start : ShuntsuStart)
| toitsuPenchan (toitsu : Toitsu) (suit : Suit) (high : Bool)
| shanpon (first second : Toitsu)
deriving BEq, DecidableEq, Repr, Fintype

namespace WaitExtraction

/-- 有限型として列挙できるすべての抽出候補。 -/
noncomputable def all : List WaitExtraction :=
  (Finset.univ : Finset WaitExtraction).toList

/-- 抽出候補が要求する牌種列。 -/
def tiles : WaitExtraction → List Tile
  | .tankiShuntsu tanki shuntsu => tanki.tiles ++ shuntsu.tiles
  | .tankiKoutsu tanki tile => tanki.tiles ++ (MentsuCandidate.koutsu tile).tiles
  | .toitsuRyanmen toitsu suit start => toitsu.tiles ++ (Taats.ryanmen suit start).tiles
  | .toitsuKanchan toitsu suit start => toitsu.tiles ++ (Taats.kanchan suit start).tiles
  | .toitsuPenchan toitsu suit high => toitsu.tiles ++ (Taats.penchan suit high).tiles
  | .shanpon first second => first.tiles ++ second.tiles

instance : HasTilePattern WaitExtraction where
  tiles := WaitExtraction.tiles

noncomputable def take (extraction : WaitExtraction) (chunk : Chunk) :
    Option (List PhysicalTile × Finset PhysicalTile) :=
  HasTilePattern.take extraction chunk

end WaitExtraction

/-- 通常形聴牌で現れる待ちの種類。 -/
inductive WaitKind
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

namespace WaitKind

/-- `WaitKind` の明示的な列挙。ドキュメント上の分類表としても使う。 -/
def all : List WaitKind :=
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

theorem exhaustive (kind : WaitKind) : kind ∈ all := by
  cases kind <;> simp [all]

end WaitKind

/-- 分解が一意か、複数の読みを持つか。 -/
inductive WaitAmbiguity
| noAmbiguity
| ambiguous
deriving BEq, DecidableEq, Repr, Fintype

/-- 完成面子を取り除いてより小さい待ちへ還元できるか。 -/
inductive WaitReducibility
| reducible
| irreducible
deriving BEq, DecidableEq, Repr, Fintype

/-- 待ちの分類ラベル。種類、曖昧性、既約性をまとめる。 -/
structure WaitClassification where
  kind : WaitKind
  ambiguity : WaitAmbiguity
  reducibility : WaitReducibility
deriving BEq, DecidableEq, Repr

/-- 待ちの分類語彙に対応する性質。 -/
def WaitKind.classification : WaitKind → WaitClassification
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
def WaitKind.reducibility (kind : WaitKind) : WaitReducibility :=
  kind.classification.reducibility

/-- この分類が複数の自然な読みを持つか。 -/
def WaitKind.ambiguity (kind : WaitKind) : WaitAmbiguity :=
  kind.classification.ambiguity
