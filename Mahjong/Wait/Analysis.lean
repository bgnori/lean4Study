import Mahjong.Wait.Specification
import Mahjong.WaitDecompositionCode

/-!
# 待ち分類の解析器

通常形の和了分解から `WaitProfile` を観測し、純粋な仕様
`WaitSpecification.Classifies` を決定する。
-/

namespace WaitAnalysis

open WaitDecompositionCode

/-!
## 牌列から観測基本形を作る

`WaitDecompositionCode.findWaitCoreExtractions` は、牌列から待ち牌ごとの核成分列と、そこから分離した完成面子を列挙する。
`waitProfilesOfCoreExtraction` は、その結果から名前付き分類に必要な観測基本形 `WaitProfile` を作る。

`observedWaitProfiles` は、牌列に対してこの変換をまとめて行う入口である。
その後、`classifyWaitProfiles` が `WaitSpecification.expectedKind` を呼び、
観測基本形の列を `WellKnownWaitKind` へ分類する。

このファイルの健全性・完全性定理は、実際の牌列から得た分類結果が、
`WaitSpecification.Classifies` で定めた宣言的仕様と一致することを示す。
-/

/-- 部品種別列から観測できる待ち基本形を列挙する。 -/
def waitProfilesOfComponentKinds
    (componentKinds : List WaitComponentKind) : List WaitProfile :=
  let has componentKind := componentKinds.contains componentKind
  (if has .tanki && has .shuntsu then [WaitProfile.tanki .shuntsu] else []) ++
  (if has .tanki && has .koutsu then [WaitProfile.tanki .koutsu] else []) ++
  (if has .toitsu && has .ryanmen then [WaitProfile.toitsuRyanmen] else []) ++
  (if has .toitsu && has .kanchan then [WaitProfile.toitsuKanchan] else []) ++
  (if has .toitsu && has .penchan then [WaitProfile.toitsuPenchan] else []) ++
  (if 2 ≤ (componentKinds.filter (fun componentKind => componentKind == .toitsu)).length then
    [WaitProfile.shanpon]
  else
    [])

/-- 核成分列を先に観測し、除去した面子は単騎の複合分類に必要な文脈としてだけ使う。 -/
def waitProfilesOfCoreExtraction
    (extraction : WaitCoreExtraction) : List WaitProfile :=
  let coreKinds := extraction.core.map fun component => component.kind
  let removedKinds := extraction.removedMentsu.map fun component => component.kind
  let hasCore componentKind := coreKinds.contains componentKind
  let hasRemoved componentKind := removedKinds.contains componentKind
  (if hasCore .tanki && !hasRemoved .shuntsu && !hasRemoved .koutsu then
    [WaitProfile.tanki .none]
  else
    []) ++
  (if hasCore .tanki && hasRemoved .shuntsu then [WaitProfile.tanki .shuntsu] else []) ++
  (if hasCore .tanki && hasRemoved .koutsu then [WaitProfile.tanki .koutsu] else []) ++
  (if hasCore .toitsu && hasCore .ryanmen then [WaitProfile.toitsuRyanmen] else []) ++
  (if hasCore .toitsu && hasCore .kanchan then [WaitProfile.toitsuKanchan] else []) ++
  (if hasCore .toitsu && hasCore .penchan then [WaitProfile.toitsuPenchan] else []) ++
  (if 2 ≤ (coreKinds.filter (fun componentKind => componentKind == .toitsu)).length then
    [WaitProfile.shanpon]
  else
    [])

/-- 牌列から得られる待ち核集合を、名前付き分類に必要な観測基本形の列へ変換する。 -/
def observedWaitProfiles (tiles : List Tile) : List WaitProfile :=
  (findWaitCoreExtractions tiles).flatMap waitProfilesOfCoreExtraction

/-- 純粋な分類仕様を実行する、基本形列上の決定手続き。 -/
def classifyWaitProfiles (profiles : List WaitProfile) : Option WellKnownWaitKind :=
  WaitSpecification.expectedKind profiles

private def basicWellKnownWaitKindOfProfile : WaitProfile → WellKnownWaitKind
  | .tanki _ => .tanki
  | .toitsuRyanmen => .toitsuRyanmen
  | .toitsuKanchan => .toitsuKanchan
  | .toitsuPenchan => .toitsuPenchan
  | .shanpon => .shanpon

/--
観測された基本形列から、人間向けの名前付き分類へ畳む前の候補分類を広めに列挙する。

`classifyWaitProfiles` は正規化済みの名前付き分類を1つ返すが、この関数は
`2234m` のように単騎核と両面形が共存する牌姿を曖昧なまま保持する。
-/
def candidateWellKnownWaitKindsOfProfiles (profiles : List WaitProfile) : List WellKnownWaitKind :=
  let basicKinds := profiles.map basicWellKnownWaitKindOfProfile
  let aliasKinds :=
    (if WaitSpecification.ContainsNobetan profiles then [.nobetan] else []) ++
    (if WaitSpecification.HasKuttsukiRyanmen profiles then [.kuttsukiRyanmen] else []) ++
    (if WaitSpecification.HasKuttsukiKanchan profiles then [.kuttsukiKanchan] else []) ++
    (if WaitSpecification.HasKuttsukiPenchan profiles then [.kuttsukiPenchan] else [])
  (basicKinds ++ aliasKinds).eraseDups

/--
観測基本形上の解析器 `classifyWaitProfiles` は、宣言的仕様 `Classifies` と一致する。

この定理は、`Specification.lean` で示した `expectedKind_iff` を、このファイルの入口名に付け替える橋渡しである。
左から右は健全性、右から左は完全性に対応する。

読むためのLean語彙: `theorem`, `↔`, `exact`。
-/
theorem classifyWaitProfiles_iff (profiles : List WaitProfile)
    (kind : WellKnownWaitKind) :
    classifyWaitProfiles profiles = some kind ↔
      WaitSpecification.Classifies profiles kind := by
  exact WaitSpecification.expectedKind_iff profiles kind

/-- 牌列に名前付き分類を与える解析器。 -/
def classifyWait (tiles : List Tile) : Option WellKnownWaitKind :=
  classifyWaitProfiles (observedWaitProfiles tiles)

/-- 牌列に対する、名前付き分類へ畳む前の候補分類。 -/
def candidateWellKnownWaitKinds (tiles : List Tile) : List WellKnownWaitKind :=
  candidateWellKnownWaitKindsOfProfiles (observedWaitProfiles tiles)

/-- 牌列が名前付き分類の仕様を満たすこと。 -/
def HasWellKnownWaitKind (tiles : List Tile) (kind : WellKnownWaitKind) : Prop :=
  WaitSpecification.Classifies (observedWaitProfiles tiles) kind

/-- `classifyWait` の健全性。 -/
theorem classifyWait_sound {tiles : List Tile} {kind : WellKnownWaitKind}
    (classified : classifyWait tiles = some kind) :
    HasWellKnownWaitKind tiles kind := by
  unfold classifyWait HasWellKnownWaitKind at *
  simpa [classifyWaitProfiles_iff] using classified

/-- `classifyWait` の完全性。 -/
theorem classifyWait_complete {tiles : List Tile} {kind : WellKnownWaitKind}
    (specified : HasWellKnownWaitKind tiles kind) :
    classifyWait tiles = some kind := by
  unfold classifyWait HasWellKnownWaitKind at *
  simpa [classifyWaitProfiles_iff] using specified

/--
牌列に対する分類結果と、牌列が名前付き分類の仕様を満たすことは同値である。

この定理により、`classifyWait` が返す分類は、牌列から観測した基本形列に対する宣言的仕様と一致する。
左から右は `classifyWait_sound`、右から左は `classifyWait_complete` が担う。
-/
theorem classifyWait_iff (tiles : List Tile) (kind : WellKnownWaitKind) :
    classifyWait tiles = some kind ↔ HasWellKnownWaitKind tiles kind :=
  ⟨classifyWait_sound, classifyWait_complete⟩

/--
聴牌の証拠を前提に、面子除去で同じ待ち構造へ縮約できるかを計算する。

名前付き分類 `WellKnownWaitKind` だけでは既約性は決まらないため、この値は具体的な牌姿に依存する。
引数に `IsTenpai tiles` を要求することで、和了不能な牌姿の既約性は構成できない。
-/
def reducibility (tiles : List Tile) (_ : WaitCompletionFinder.IsTenpai tiles) :
    WaitReducibility :=
  if WaitDecompositionCode.CanReduceMentsuPreservingWaitCores tiles then
    .reducible
  else
    .irreducible

/--
任意の牌列について、聴牌なら可約・既約を判定し、非聴牌なら `none` を返す。

`reducibility` 自体は聴牌の証拠を要求するため、条件分岐に `tenpai` と名前を付け、
聴牌側の分岐で得られる証拠をそのまま渡す。これにより、可約・既約という分類を
和了可能な待ちが存在する牌列だけに制限しつつ、一般の牌列から呼べる入口にしている。

読むためのLean語彙: `Option`, 証拠付き `if`, `some`, `none`。
-/
def determineReducibility (tiles : List Tile) : Option WaitReducibility :=
  if tenpai : WaitCompletionFinder.IsTenpai tiles then
    some (reducibility tiles tenpai)
  else
    none

/--
`reducibility` が「可約」と判定することは、待ち核集合を保ったまま完成面子を除去できることと同値である。

左から右は計算結果に可約である根拠があること、右から左は面子を除去できれば計算も可約を返すことを表す。
証明では `reducibility` の定義を展開し、条件分岐の条件そのものとの同値を `simp` で確認する。

読むためのLean語彙: `theorem`, `↔`, `simp`。
-/
theorem reducibility_eq_reducible_iff (tiles : List Tile)
    (tenpai : WaitCompletionFinder.IsTenpai tiles) :
    reducibility tiles tenpai = .reducible ↔
      WaitDecompositionCode.CanReduceMentsuPreservingWaitCores tiles := by
  simp [reducibility]

/--
`reducibility` が「既約」と判定することは、待ち核集合を保ったまま除去できる完成面子がないことと同値である。

既約性を新しい探索条件として重ねるのではなく、可約性の条件
`CanReduceMentsuPreservingWaitCores` の否定として特徴づけている。
証明では `reducibility` の定義を展開し、条件分岐が可約でない場合に限って `.irreducible` を返すことを
`simp` で確認する。

読むためのLean語彙: `theorem`, `↔`, `¬`, `simp`。
-/
theorem reducibility_eq_irreducible_iff (tiles : List Tile)
    (tenpai : WaitCompletionFinder.IsTenpai tiles) :
    reducibility tiles tenpai = .irreducible ↔
      ¬WaitDecompositionCode.CanReduceMentsuPreservingWaitCores tiles := by
  simp [reducibility]

end WaitAnalysis
