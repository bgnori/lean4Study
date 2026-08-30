import Mahjong.Wait

/-!
# 待ち分類の仕様

解析器が牌列から観測する基本形を `WaitProfile` とし、その観測列がどの
`WaitKind` に属するかを命題 `Classifies` で宣言的に定める。
このモジュールは和了分解の列挙方法や分類アルゴリズムには依存しない。
-/

/-- 1つの和了分解から観測される待ちの基本形。 -/
inductive WaitProfile
| tankiShuntsu
| tankiKoutsu
| toitsuRyanmen
| toitsuKanchan
| toitsuPenchan
| shanpon
deriving BEq, DecidableEq, Repr

namespace WaitSpecification

/-- 刻子を伴う単騎と、指定した対子+ターツの読みが共存すること。 -/
def HasKuttsuki (profiles : List WaitProfile) (taatsuProfile : WaitProfile) : Prop :=
  profiles.contains .tankiKoutsu = true ∧ profiles.contains taatsuProfile = true

instance (profiles : List WaitProfile) (taatsuProfile : WaitProfile) :
    Decidable (HasKuttsuki profiles taatsuProfile) := by
  unfold HasKuttsuki
  infer_instance

/-- 両面くっつきの2つの読みが共存すること。 -/
abbrev HasKuttsukiRyanmen (profiles : List WaitProfile) : Prop :=
  HasKuttsuki profiles .toitsuRyanmen

/-- 嵌張くっつきの2つの読みが共存すること。 -/
abbrev HasKuttsukiKanchan (profiles : List WaitProfile) : Prop :=
  HasKuttsuki profiles .toitsuKanchan

/-- 辺張くっつきの2つの読みが共存すること。 -/
abbrev HasKuttsukiPenchan (profiles : List WaitProfile) : Prop :=
  HasKuttsuki profiles .toitsuPenchan

/--
観測列がノベタンとして読める部分を含むこと。

これは牌姿全体の分類名ではなく、人間向けの別名として使う。ほかの読みが同時に
存在しても、単騎+順子の読みが2つ以上あれば成立する。
-/
def HasNobetanReading (profiles : List WaitProfile) : Prop :=
  2 ≤ profiles.count .tankiShuntsu

instance (profiles : List WaitProfile) : Decidable (HasNobetanReading profiles) := by
  unfold HasNobetanReading
  infer_instance

/-- 牌姿全体をノベタンと分類するための、単騎+順子だけからなる狭義の条件。 -/
def IsNobetan (profiles : List WaitProfile) : Prop :=
  HasNobetanReading profiles ∧ ∀ profile ∈ profiles, profile = .tankiShuntsu

instance (profiles : List WaitProfile) : Decidable (IsNobetan profiles) := by
  unfold IsNobetan
  infer_instance

/--
観測された基本形列に期待する名前付き分類を与える宣言的な規則。

各コンストラクタは分類が成立する理由を保持する。くっつきは優先順位を明示し、
それ以外では狭義のノベタンを先に認識してから、正規化済み観測列の先頭を使う。
この命題は下の決定手続き `expectedKind` を参照しない。
-/
inductive Classifies : List WaitProfile → WaitKind → Prop
| kuttsukiRyanmen {profiles}
    (has : HasKuttsukiRyanmen profiles) : Classifies profiles .kuttsukiRyanmen
| kuttsukiKanchan {profiles}
    (noRyanmen : ¬HasKuttsukiRyanmen profiles)
    (has : HasKuttsukiKanchan profiles) : Classifies profiles .kuttsukiKanchan
| kuttsukiPenchan {profiles}
    (noRyanmen : ¬HasKuttsukiRyanmen profiles)
    (noKanchan : ¬HasKuttsukiKanchan profiles)
    (has : HasKuttsukiPenchan profiles) : Classifies profiles .kuttsukiPenchan
| nobetan {profiles}
    (noRyanmen : ¬HasKuttsukiRyanmen profiles)
    (noKanchan : ¬HasKuttsukiKanchan profiles)
    (noPenchan : ¬HasKuttsukiPenchan profiles)
    (has : IsNobetan profiles) : Classifies profiles .nobetan
| tankiShuntsu {rest}
    (noRyanmen : ¬HasKuttsukiRyanmen (.tankiShuntsu :: rest))
    (noKanchan : ¬HasKuttsukiKanchan (.tankiShuntsu :: rest))
    (noPenchan : ¬HasKuttsukiPenchan (.tankiShuntsu :: rest))
    (noNobetan : ¬IsNobetan (.tankiShuntsu :: rest)) :
    Classifies (.tankiShuntsu :: rest) .tankiShuntsu
  | tankiKoutsu {rest}
    (noRyanmen : ¬HasKuttsukiRyanmen (.tankiKoutsu :: rest))
    (noKanchan : ¬HasKuttsukiKanchan (.tankiKoutsu :: rest))
    (noPenchan : ¬HasKuttsukiPenchan (.tankiKoutsu :: rest))
    (noNobetan : ¬IsNobetan (.tankiKoutsu :: rest)) :
    Classifies (.tankiKoutsu :: rest) .tankiKoutsu
  | toitsuRyanmen {rest}
    (noRyanmen : ¬HasKuttsukiRyanmen (.toitsuRyanmen :: rest))
    (noKanchan : ¬HasKuttsukiKanchan (.toitsuRyanmen :: rest))
    (noPenchan : ¬HasKuttsukiPenchan (.toitsuRyanmen :: rest))
    (noNobetan : ¬IsNobetan (.toitsuRyanmen :: rest)) :
    Classifies (.toitsuRyanmen :: rest) .toitsuRyanmen
  | toitsuKanchan {rest}
    (noRyanmen : ¬HasKuttsukiRyanmen (.toitsuKanchan :: rest))
    (noKanchan : ¬HasKuttsukiKanchan (.toitsuKanchan :: rest))
    (noPenchan : ¬HasKuttsukiPenchan (.toitsuKanchan :: rest))
    (noNobetan : ¬IsNobetan (.toitsuKanchan :: rest)) :
    Classifies (.toitsuKanchan :: rest) .toitsuKanchan
  | toitsuPenchan {rest}
    (noRyanmen : ¬HasKuttsukiRyanmen (.toitsuPenchan :: rest))
    (noKanchan : ¬HasKuttsukiKanchan (.toitsuPenchan :: rest))
    (noPenchan : ¬HasKuttsukiPenchan (.toitsuPenchan :: rest))
    (noNobetan : ¬IsNobetan (.toitsuPenchan :: rest)) :
    Classifies (.toitsuPenchan :: rest) .toitsuPenchan
  | shanpon {rest}
    (noRyanmen : ¬HasKuttsukiRyanmen (.shanpon :: rest))
    (noKanchan : ¬HasKuttsukiKanchan (.shanpon :: rest))
    (noPenchan : ¬HasKuttsukiPenchan (.shanpon :: rest))
    (noNobetan : ¬IsNobetan (.shanpon :: rest)) :
    Classifies (.shanpon :: rest) .shanpon

/--
観測された基本形列に期待する名前付き分類を与える参照仕様。

複数のくっつき条件が同時に成立する場合は両面、嵌張、辺張の順に正規化する。
それ以外は狭義のノベタンを認識してから、正規化済み観測列の先頭で基本形を定める。
-/
def expectedKind (profiles : List WaitProfile) : Option WaitKind :=
  if HasKuttsukiRyanmen profiles then
    some WaitKind.kuttsukiRyanmen
  else if HasKuttsukiKanchan profiles then
    some WaitKind.kuttsukiKanchan
  else if HasKuttsukiPenchan profiles then
    some WaitKind.kuttsukiPenchan
  else if IsNobetan profiles then
    some WaitKind.nobetan
  else match profiles with
    | [] => none
    | WaitProfile.tankiShuntsu :: _ => some WaitKind.tankiShuntsu
    | WaitProfile.tankiKoutsu :: _ => some WaitKind.tankiKoutsu
    | WaitProfile.toitsuRyanmen :: _ => some WaitKind.toitsuRyanmen
    | WaitProfile.toitsuKanchan :: _ => some WaitKind.toitsuKanchan
    | WaitProfile.toitsuPenchan :: _ => some WaitKind.toitsuPenchan
    | WaitProfile.shanpon :: _ => some WaitKind.shanpon

/-- `expectedKind` は宣言的な分類規則を健全かつ完全に決定する。 -/
theorem expectedKind_iff (profiles : List WaitProfile) (kind : WaitKind) :
    expectedKind profiles = some kind ↔ Classifies profiles kind := by
  constructor
  · intro result
    unfold expectedKind at result
    split at result <;> rename_i kuttsukiRyanmen
    · cases result
      exact .kuttsukiRyanmen kuttsukiRyanmen
    · split at result <;> rename_i kuttsukiKanchan
      · cases result
        exact .kuttsukiKanchan kuttsukiRyanmen kuttsukiKanchan
      · split at result <;> rename_i kuttsukiPenchan
        · cases result
          exact .kuttsukiPenchan kuttsukiRyanmen kuttsukiKanchan kuttsukiPenchan
        · split at result <;> rename_i nobetan
          · cases result
            exact .nobetan kuttsukiRyanmen kuttsukiKanchan kuttsukiPenchan nobetan
          · cases profiles with
            | nil => simp at result
            | cons profile rest =>
                cases profile <;> cases result
                · exact .tankiShuntsu kuttsukiRyanmen kuttsukiKanchan kuttsukiPenchan nobetan
                · exact .tankiKoutsu kuttsukiRyanmen kuttsukiKanchan kuttsukiPenchan nobetan
                · exact .toitsuRyanmen kuttsukiRyanmen kuttsukiKanchan kuttsukiPenchan nobetan
                · exact .toitsuKanchan kuttsukiRyanmen kuttsukiKanchan kuttsukiPenchan nobetan
                · exact .toitsuPenchan kuttsukiRyanmen kuttsukiKanchan kuttsukiPenchan nobetan
                · exact .shanpon kuttsukiRyanmen kuttsukiKanchan kuttsukiPenchan nobetan
  · intro classified
    cases classified <;> simp_all [expectedKind]

example : HasNobetanReading [.tankiShuntsu, .tankiShuntsu] := by decide

-- ほかの読みと共存しても、「ノベタン読みを含む」という別名は利用できる。
example : HasNobetanReading [.tankiShuntsu, .shanpon, .tankiShuntsu] := by decide

example : ¬IsNobetan [.tankiShuntsu, .shanpon, .tankiShuntsu] := by decide

end WaitSpecification
