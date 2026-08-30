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
観測された基本形列に期待する名前付き分類を与える参照仕様。

複数のくっつき条件が同時に成立する場合は両面、嵌張、辺張の順に正規化する。
それ以外は正規化済み観測列の先頭で基本形を定め、単騎+順子が複数あれば
ノベタンとする。
-/
def expectedKind (profiles : List WaitProfile) : Option WaitKind :=
  if HasKuttsukiRyanmen profiles then
    some WaitKind.kuttsukiRyanmen
  else if HasKuttsukiKanchan profiles then
    some WaitKind.kuttsukiKanchan
  else if HasKuttsukiPenchan profiles then
    some WaitKind.kuttsukiPenchan
  else match profiles with
    | [] => none
    | WaitProfile.tankiShuntsu :: rest =>
        if rest.isEmpty then some WaitKind.tankiShuntsu else some WaitKind.nobetan
    | WaitProfile.tankiKoutsu :: _ => some WaitKind.tankiKoutsu
    | WaitProfile.toitsuRyanmen :: _ => some WaitKind.toitsuRyanmen
    | WaitProfile.toitsuKanchan :: _ => some WaitKind.toitsuKanchan
    | WaitProfile.toitsuPenchan :: _ => some WaitKind.toitsuPenchan
    | WaitProfile.shanpon :: _ => some WaitKind.shanpon

/-- 基本形列が名前付き分類に属するという、解析器から独立した仕様命題。 -/
def Classifies (profiles : List WaitProfile) (kind : WaitKind) : Prop :=
  expectedKind profiles = some kind

end WaitSpecification
