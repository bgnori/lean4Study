import Mahjong.Wait

/-!
# 待ち分類の仕様

解析器が牌列から観測する内部基本形を `WaitProfile` とし、その観測列がどの
名前付き分類 `WellKnownWaitKind` に属するかを命題 `Classifies` で宣言的に定める。
このモジュールは和了分解の列挙方法や分類アルゴリズムには依存しない。
-/

/-!
## 待ち核集合から名前付き分類へ

このモジュールでは、待ち核集合そのものではなく、分類に必要な情報だけを取り出した
観測基本形 `WaitProfile` の列を扱う。

`WaitProfile` は、単騎、対子+ターツ形、双碰のような基本形を表す。
単騎については、分離された完成面子がなかったか、順子だったか、刻子だったかを
`WaitProfileMentsu` として残す。これはノベタンやくっつきのような名前付き分類を
判定するために必要な文脈である。

`Classifies` は、観測基本形の列がどの `WellKnownWaitKind` に属するかを、計算器から独立した
宣言的な規則として定める。`expectedKind` は同じ規則を実行できる形にした参照実装で、
`expectedKind_iff` が両者の一致を保証する。
-/

/-- 単騎核と一緒に分離された完成面子の文脈。純粋な1枚単騎では `none`。 -/
inductive WaitProfileMentsu
| none
| shuntsu
| koutsu
deriving BEq, DecidableEq, Repr

/-- 既約な待ち核から観測される内部基本形。くっつきやノベタン判定に必要な文脈は引数に残す。 -/
inductive WaitProfile
| tanki (mentsu : WaitProfileMentsu)
| toitsuRyanmen
| toitsuKanchan
| toitsuPenchan
| shanpon
deriving BEq, DecidableEq, Repr

namespace WaitSpecification

/-!
## 通称・複合分類を認識する補助条件

`HasKuttsuki...` 系は、刻子文脈を伴う単騎核と、対子+ターツ形が同時に観測されることを表す。
`HasNobetanReading` は、順子文脈を伴う単騎核が2つ以上あることを表す。

`HasNobetanReading` は名前に `Reading` を含むが、ここでは麻雀一般の「待ち読み」ではなく、
名前付き分類 `nobetan` を使える条件として読む。
`IsNobetan` はさらに狭く、観測列全体が順子文脈を伴う単騎核だけからなることを要求する。
-/

/-- 刻子文脈を伴う単騎核と、指定した対子+ターツ形が共存すること。 -/
def HasKuttsuki (profiles : List WaitProfile) (taatsuProfile : WaitProfile) : Prop :=
  profiles.contains (.tanki .koutsu) = true ∧ profiles.contains taatsuProfile = true

instance (profiles : List WaitProfile) (taatsuProfile : WaitProfile) :
    Decidable (HasKuttsuki profiles taatsuProfile) := by
  unfold HasKuttsuki
  infer_instance

/-- 両面くっつきに必要な2つの基本形が共存すること。 -/
abbrev HasKuttsukiRyanmen (profiles : List WaitProfile) : Prop :=
  HasKuttsuki profiles .toitsuRyanmen

/-- 嵌張くっつきに必要な2つの基本形が共存すること。 -/
abbrev HasKuttsukiKanchan (profiles : List WaitProfile) : Prop :=
  HasKuttsuki profiles .toitsuKanchan

/-- 辺張くっつきに必要な2つの基本形が共存すること。 -/
abbrev HasKuttsukiPenchan (profiles : List WaitProfile) : Prop :=
  HasKuttsuki profiles .toitsuPenchan

/--
観測列がノベタン相当の部分を含むこと。

これは牌姿全体の分類名ではなく、人間向けの別名として使う。ほかの基本形が同時に
存在しても、順子文脈を伴う単騎核が2つ以上あれば成立する。
-/
def HasNobetanReading (profiles : List WaitProfile) : Prop :=
  2 ≤ profiles.count (.tanki .shuntsu)

instance (profiles : List WaitProfile) : Decidable (HasNobetanReading profiles) := by
  unfold HasNobetanReading
  infer_instance

/-- 牌姿全体をノベタンと分類するための、順子文脈を伴う単騎核だけからなる狭義の条件。 -/
def IsNobetan (profiles : List WaitProfile) : Prop :=
  HasNobetanReading profiles ∧ ∀ profile ∈ profiles, profile = .tanki .shuntsu

instance (profiles : List WaitProfile) : Decidable (IsNobetan profiles) := by
  unfold IsNobetan
  infer_instance

/-!
## 名前付き分類の宣言的仕様と参照実装

`Classifies` は、観測基本形の列がどの名前付き分類に属するかを命題として定める。
各コンストラクタは、その分類を選ぶために必要な条件を明示的に持つ。

`expectedKind` は、同じ規則を実行可能な決定手続きとして書いたものである。
複数の条件が同時に成立する場合は、くっつき両面、くっつき嵌張、くっつき辺張、狭義ノベタン、
基本形の順に名前付き分類を選ぶ。
-/

/--
観測された基本形列に期待する名前付き分類を与える宣言的な規則。

各コンストラクタは分類が成立する理由を保持する。くっつきは優先順位を明示し、
それ以外では狭義のノベタンを先に認識してから、正規化済み観測列の先頭を使う。
この命題は下の決定手続き `expectedKind` を参照しない。
-/
inductive Classifies : List WaitProfile → WellKnownWaitKind → Prop
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
| tanki {mentsu rest}
  (noRyanmen : ¬HasKuttsukiRyanmen (WaitProfile.tanki mentsu :: rest))
  (noKanchan : ¬HasKuttsukiKanchan (WaitProfile.tanki mentsu :: rest))
  (noPenchan : ¬HasKuttsukiPenchan (WaitProfile.tanki mentsu :: rest))
  (noNobetan : ¬IsNobetan (WaitProfile.tanki mentsu :: rest)) :
  Classifies (WaitProfile.tanki mentsu :: rest) WellKnownWaitKind.tanki
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
def expectedKind (profiles : List WaitProfile) : Option WellKnownWaitKind :=
  if HasKuttsukiRyanmen profiles then
    some WellKnownWaitKind.kuttsukiRyanmen
  else if HasKuttsukiKanchan profiles then
    some WellKnownWaitKind.kuttsukiKanchan
  else if HasKuttsukiPenchan profiles then
    some WellKnownWaitKind.kuttsukiPenchan
  else if IsNobetan profiles then
    some WellKnownWaitKind.nobetan
  else match profiles with
    | [] => none
    | WaitProfile.tanki _ :: _ => some WellKnownWaitKind.tanki
    | WaitProfile.toitsuRyanmen :: _ => some WellKnownWaitKind.toitsuRyanmen
    | WaitProfile.toitsuKanchan :: _ => some WellKnownWaitKind.toitsuKanchan
    | WaitProfile.toitsuPenchan :: _ => some WellKnownWaitKind.toitsuPenchan
    | WaitProfile.shanpon :: _ => some WellKnownWaitKind.shanpon

/--
`expectedKind` が返す名前付き分類と、宣言的仕様 `Classifies` は一致する。

左辺は実行できる参照実装で、右辺は分類が成立する理由を保持する仕様である。
この定理により、参照実装が分類規則を過不足なく判定していることが分かる。
左から右は健全性、右から左は完全性に対応する。

読むためのLean語彙: `theorem`, `↔`, `constructor`, `intro`, `unfold`, `split`, `cases`, `exact`, `simp_all`。
-/
theorem expectedKind_iff (profiles : List WaitProfile) (kind : WellKnownWaitKind) :
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
                · exact .tanki kuttsukiRyanmen kuttsukiKanchan kuttsukiPenchan nobetan
                · exact .toitsuRyanmen kuttsukiRyanmen kuttsukiKanchan kuttsukiPenchan nobetan
                · exact .toitsuKanchan kuttsukiRyanmen kuttsukiKanchan kuttsukiPenchan nobetan
                · exact .toitsuPenchan kuttsukiRyanmen kuttsukiKanchan kuttsukiPenchan nobetan
                · exact .shanpon kuttsukiRyanmen kuttsukiKanchan kuttsukiPenchan nobetan
  · intro classified
    cases classified <;> simp_all [expectedKind]

example : HasNobetanReading [.tanki .shuntsu, .tanki .shuntsu] := by decide

-- ほかの読みと共存しても、「ノベタン読みを含む」という別名は利用できる。
example : HasNobetanReading [.tanki .shuntsu, .shanpon, .tanki .shuntsu] := by decide

example : ¬IsNobetan [.tanki .shuntsu, .shanpon, .tanki .shuntsu] := by decide

end WaitSpecification
