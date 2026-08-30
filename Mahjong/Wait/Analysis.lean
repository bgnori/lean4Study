import Mahjong.Wait.Specification
import Mahjong.DecompositionCode

/-!
# 待ち分類の解析器

通常形の和了分解から `WaitProfile` を観測し、純粋な仕様
`WaitSpecification.Classifies` を決定する。
-/

namespace WaitAnalysis

open DecompositionCode

/-- 形部品列から観測できる待ち基本形を列挙する。 -/
def waitProfilesOfComponents (components : List DecompositionComponent) : List WaitProfile :=
  let has component := components.contains component
  (if has .tanki && has .shuntsu then [WaitProfile.tankiShuntsu] else []) ++
  (if has .tanki && has .koutsu then [WaitProfile.tankiKoutsu] else []) ++
  (if has .toitsu && has .ryanmen then [WaitProfile.toitsuRyanmen] else []) ++
  (if has .toitsu && has .kanchan then [WaitProfile.toitsuKanchan] else []) ++
  (if has .toitsu && has .penchan then [WaitProfile.toitsuPenchan] else []) ++
  (if 2 ≤ (components.filter (fun component => component == .toitsu)).length then
    [WaitProfile.shanpon]
  else
    [])

/-- 通常形の和了分解から得られる待ち基本形の正規化済み観測列。 -/
def observedWaitProfiles (tiles : List Tile) : List WaitProfile :=
  (findAbstractDecompositionExtractions tiles).flatMap fun extraction =>
    waitProfilesOfComponents extraction.components

/-- 純粋な分類仕様を実行する、基本形列上の決定手続き。 -/
def classifyWaitProfiles (profiles : List WaitProfile) : Option WaitKind :=
  WaitSpecification.expectedKind profiles

/-- 基本形上の解析器は宣言的な分類仕様に対して健全かつ完全である。 -/
theorem classifyWaitProfiles_iff (profiles : List WaitProfile)
    (kind : WaitKind) :
    classifyWaitProfiles profiles = some kind ↔
      WaitSpecification.Classifies profiles kind := by
  rfl

/-- 牌列に名前付き分類を与える解析器。 -/
def classifyWait (tiles : List Tile) : Option WaitKind :=
  classifyWaitProfiles (observedWaitProfiles tiles)

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

end WaitAnalysis
