import Mahjong.FourTileWait

/-!
# 4枚待ち分類の仕様

解析器が牌列から観測する基本形を `FourTileProfile` とし、その観測列がどの
`FourTileWaitKind` に属するかを命題 `Classifies` で宣言的に定める。
このモジュールは和了分解の列挙方法や分類アルゴリズムには依存しない。
-/

/-- 1つの和了分解から観測される、4枚待ちの基本形。 -/
inductive FourTileProfile
| tankiShuntsu
| tankiKoutsu
| toitsuRyanmen
| toitsuKanchan
| toitsuPenchan
| shanpon
deriving BEq, DecidableEq, Repr

namespace FourTileSpecification

/-- 両面くっつきの2つの読みが共存すること。 -/
def HasKuttsukiRyanmen (profiles : List FourTileProfile) : Prop :=
  profiles.contains .tankiKoutsu = true ∧ profiles.contains .toitsuRyanmen = true

/-- 嵌張くっつきの2つの読みが共存すること。 -/
def HasKuttsukiKanchan (profiles : List FourTileProfile) : Prop :=
  profiles.contains .tankiKoutsu = true ∧ profiles.contains .toitsuKanchan = true

/-- 辺張くっつきの2つの読みが共存すること。 -/
def HasKuttsukiPenchan (profiles : List FourTileProfile) : Prop :=
  profiles.contains .tankiKoutsu = true ∧ profiles.contains .toitsuPenchan = true

/--
観測された基本形列に期待する名前付き分類を与える参照仕様。

複数のくっつき条件が同時に成立する場合は両面、嵌張、辺張の順に正規化する。
それ以外は正規化済み観測列の先頭で基本形を定め、単騎+順子が複数あれば
ノベタンとする。
-/
def expectedKind (profiles : List FourTileProfile) : Option FourTileWaitKind :=
  if profiles.contains .tankiKoutsu && profiles.contains .toitsuRyanmen then
    some .kuttsukiRyanmen
  else if profiles.contains .tankiKoutsu && profiles.contains .toitsuKanchan then
    some .kuttsukiKanchan
  else if profiles.contains .tankiKoutsu && profiles.contains .toitsuPenchan then
    some .kuttsukiPenchan
  else match profiles with
    | [] => none
    | .tankiShuntsu :: rest =>
        if rest.isEmpty then some .tankiShuntsu else some .nobetan
    | .tankiKoutsu :: _ => some .tankiKoutsu
    | .toitsuRyanmen :: _ => some .toitsuRyanmen
    | .toitsuKanchan :: _ => some .toitsuKanchan
    | .toitsuPenchan :: _ => some .toitsuPenchan
    | .shanpon :: _ => some .shanpon

/-- 基本形列が名前付き分類に属するという、解析器から独立した仕様命題。 -/
def Classifies (profiles : List FourTileProfile) (kind : FourTileWaitKind) : Prop :=
  expectedKind profiles = some kind

end FourTileSpecification
