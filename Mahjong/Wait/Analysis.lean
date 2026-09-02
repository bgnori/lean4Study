import Mahjong.Wait.Specification
import Mahjong.WaitReadingCode

/-!
# 待ち分類の解析器

通常形の和了分解から `WaitProfile` を観測し、純粋な仕様
`WaitSpecification.Classifies` を決定する。
-/

namespace WaitAnalysis

open WaitReadingCode

/-- 部品種別列から観測できる待ち基本形を列挙する。 -/
def waitProfilesOfComponentKinds
    (componentKinds : List WaitReadingComponentKind) : List WaitProfile :=
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

/-- 既約核を先に読み、除去した面子は単騎の複合分類に必要な文脈としてだけ使う。 -/
def waitProfilesOfIrreducibleReading
    (reading : IrreducibleWaitReading) : List WaitProfile :=
  let coreKinds := reading.core.map fun component => component.kind
  let removedKinds := reading.removedMentsu.map fun component => component.kind
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

/-- 通常形の和了分解から得られる待ち基本形の正規化済み観測列。 -/
def observedWaitProfiles (tiles : List Tile) : List WaitProfile :=
  (findIrreducibleWaitReadings tiles).flatMap waitProfilesOfIrreducibleReading

/-- 純粋な分類仕様を実行する、基本形列上の決定手続き。 -/
def classifyWaitProfiles (profiles : List WaitProfile) : Option WaitKind :=
  WaitSpecification.expectedKind profiles

private def basicWaitKindOfProfile : WaitProfile → WaitKind
  | .tanki _ => .tanki
  | .toitsuRyanmen => .toitsuRyanmen
  | .toitsuKanchan => .toitsuKanchan
  | .toitsuPenchan => .toitsuPenchan
  | .shanpon => .shanpon

/--
観測された基本形列から、人間向けの代表分類へ畳む前の候補分類を広めに列挙する。

`classifyWaitProfiles` は正規化済みの代表分類を1つ返すが、この関数は
`2234m` のように単騎読みと両面読みが共存する牌姿を曖昧なまま保持する。
-/
def candidateWaitKindsOfProfiles (profiles : List WaitProfile) : List WaitKind :=
  let basicKinds := profiles.map basicWaitKindOfProfile
  let aliasKinds :=
    (if WaitSpecification.HasNobetanReading profiles then [.nobetan] else []) ++
    (if WaitSpecification.HasKuttsukiRyanmen profiles then [.kuttsukiRyanmen] else []) ++
    (if WaitSpecification.HasKuttsukiKanchan profiles then [.kuttsukiKanchan] else []) ++
    (if WaitSpecification.HasKuttsukiPenchan profiles then [.kuttsukiPenchan] else [])
  (basicKinds ++ aliasKinds).eraseDups

/-- 基本形上の解析器は宣言的な分類仕様に対して健全かつ完全である。 -/
theorem classifyWaitProfiles_iff (profiles : List WaitProfile)
    (kind : WaitKind) :
    classifyWaitProfiles profiles = some kind ↔
      WaitSpecification.Classifies profiles kind := by
  exact WaitSpecification.expectedKind_iff profiles kind

/-- 牌列に名前付き分類を与える解析器。 -/
def classifyWait (tiles : List Tile) : Option WaitKind :=
  classifyWaitProfiles (observedWaitProfiles tiles)

/-- 牌列に対する、代表分類へ畳む前の候補分類。 -/
def candidateWaitKinds (tiles : List Tile) : List WaitKind :=
  candidateWaitKindsOfProfiles (observedWaitProfiles tiles)

/-- 牌列が名前付き分類の仕様を満たすこと。 -/
def HasWaitKind (tiles : List Tile) (kind : WaitKind) : Prop :=
  WaitSpecification.Classifies (observedWaitProfiles tiles) kind

/-- `classifyWait` の健全性。 -/
theorem classifyWait_sound {tiles : List Tile} {kind : WaitKind}
    (classified : classifyWait tiles = some kind) :
    HasWaitKind tiles kind := by
  unfold classifyWait HasWaitKind at *
  simpa [classifyWaitProfiles_iff] using classified

/-- `classifyWait` の完全性。 -/
theorem classifyWait_complete {tiles : List Tile} {kind : WaitKind}
    (specified : HasWaitKind tiles kind) :
    classifyWait tiles = some kind := by
  unfold classifyWait HasWaitKind at *
  simpa [classifyWaitProfiles_iff] using specified

/-- 健全性と完全性をまとめた特徴付け。 -/
theorem classifyWait_iff (tiles : List Tile) (kind : WaitKind) :
    classifyWait tiles = some kind ↔ HasWaitKind tiles kind :=
  ⟨classifyWait_sound, classifyWait_complete⟩

/--
聴牌の証拠を前提に、面子除去で同じ待ち構造へ縮約できるかを計算する。

`WaitKind` だけでは既約性は決まらないため、この値は具体的な牌姿に依存する。
引数に `IsTenpai tiles` を要求することで、和了不能な牌姿の既約性は構成できない。
-/
def reducibility (tiles : List Tile) (_ : WaitCompletionFinder.IsTenpai tiles) :
    WaitReducibility :=
  if WaitReadingCode.CanReduceMentsuPreservingWaitCores tiles then
    .reducible
  else
    .irreducible

/-- 非聴牌を `none` として明示する、既約性の決定手続き。 -/
def determineReducibility (tiles : List Tile) : Option WaitReducibility :=
  if tenpai : WaitCompletionFinder.IsTenpai tiles then
    some (reducibility tiles tenpai)
  else
    none

/-- 計算結果が可約であることは、面子除去可能性と同値である。 -/
theorem reducibility_eq_reducible_iff (tiles : List Tile)
    (tenpai : WaitCompletionFinder.IsTenpai tiles) :
    reducibility tiles tenpai = .reducible ↔
      WaitReadingCode.CanReduceMentsuPreservingWaitCores tiles := by
  simp [reducibility]

/-- 計算結果が既約であることは、面子除去不能性と同値である。 -/
theorem reducibility_eq_irreducible_iff (tiles : List Tile)
    (tenpai : WaitCompletionFinder.IsTenpai tiles) :
    reducibility tiles tenpai = .irreducible ↔
      ¬WaitReadingCode.CanReduceMentsuPreservingWaitCores tiles := by
  simp [reducibility]

end WaitAnalysis
