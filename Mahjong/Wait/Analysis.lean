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
  (if has .tanki && has .shuntsu then [WaitProfile.tanki .shuntsu] else []) ++
  (if has .tanki && has .koutsu then [WaitProfile.tanki .koutsu] else []) ++
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
  exact WaitSpecification.expectedKind_iff profiles kind

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

/--
聴牌の証拠を前提に、面子除去で同じ待ち構造へ縮約できるかを計算する。

`WaitKind` だけでは既約性は決まらないため、この値は具体的な牌姿に依存する。
引数に `IsTenpai tiles` を要求することで、和了不能な牌姿の既約性は構成できない。
-/
def reducibility (tiles : List Tile) (_ : DecompositionFinder.IsTenpai tiles) :
    WaitReducibility :=
  if DecompositionFinder.CanReduceMentsu tiles then .reducible else .irreducible

/-- 非聴牌を `none` として明示する、既約性の決定手続き。 -/
def determineReducibility (tiles : List Tile) : Option WaitReducibility :=
  if tenpai : DecompositionFinder.IsTenpai tiles then
    some (reducibility tiles tenpai)
  else
    none

/-- 計算結果が可約であることは、面子除去可能性と同値である。 -/
theorem reducibility_eq_reducible_iff (tiles : List Tile)
    (tenpai : DecompositionFinder.IsTenpai tiles) :
    reducibility tiles tenpai = .reducible ↔
      DecompositionFinder.CanReduceMentsu tiles := by
  simp [reducibility]

/-- 計算結果が既約であることは、面子除去不能性と同値である。 -/
theorem reducibility_eq_irreducible_iff (tiles : List Tile)
    (tenpai : DecompositionFinder.IsTenpai tiles) :
    reducibility tiles tenpai = .irreducible ↔
      ¬DecompositionFinder.CanReduceMentsu tiles := by
  simp [reducibility]

end WaitAnalysis
