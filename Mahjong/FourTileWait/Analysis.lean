import Mahjong.FourTileWait.Specification
import Mahjong.Wait.Analysis

/-!
# 4枚待ち分類の解析器

待ち分類の解析本体は `Mahjong.Wait.Analysis` に置く。
このモジュールは4枚牌列であることを確認するラッパーと、4枚ケースのテスト例を提供する。
-/

namespace FourTileAnalysis

open DecompositionCode

abbrev fourTileProfilesOfComponents : List DecompositionComponent → List FourTileProfile :=
  WaitAnalysis.waitProfilesOfComponents

abbrev observedFourTileProfiles (tiles : List Tile) : List FourTileProfile :=
  WaitAnalysis.observedWaitProfiles tiles

abbrev classifyFourTileProfiles (profiles : List FourTileProfile) : Option FourTileWaitKind :=
  WaitAnalysis.classifyWaitProfiles profiles

/-- 4枚牌列に名前付き分類を与えるテスト用ラッパー。 -/
def classifyFourTile (tiles : List Tile) : Option FourTileWaitKind :=
  if tiles.length = fourTileHandSize then
    WaitAnalysis.classifyWait tiles
  else
    none

/-- 牌列が名前付き4枚分類の仕様を満たすこと。 -/
def HasFourTileKind (tiles : List Tile) (kind : FourTileWaitKind) : Prop :=
  tiles.length = fourTileHandSize ∧
    WaitSpecification.Classifies (WaitAnalysis.observedWaitProfiles tiles) kind

/-- `classifyFourTile` の健全性。 -/
theorem classifyFourTile_sound {tiles : List Tile} {kind : FourTileWaitKind}
    (classified : classifyFourTile tiles = some kind) :
    HasFourTileKind tiles kind := by
  by_cases length : tiles.length = fourTileHandSize
  · unfold classifyFourTile at classified
    simp [length] at classified
    exact ⟨length, WaitAnalysis.classifyWait_sound classified⟩
  · unfold classifyFourTile at classified
    simp [length] at classified

/-- `classifyFourTile` の完全性。 -/
theorem classifyFourTile_complete {tiles : List Tile} {kind : FourTileWaitKind}
    (specified : HasFourTileKind tiles kind) :
    classifyFourTile tiles = some kind := by
  rcases specified with ⟨length, classified⟩
  unfold classifyFourTile
  simp [length, WaitAnalysis.classifyWait_complete classified]

/-- 健全性と完全性をまとめた特徴付け。 -/
theorem classifyFourTile_iff (tiles : List Tile) (kind : FourTileWaitKind) :
    classifyFourTile tiles = some kind ↔ HasFourTileKind tiles kind :=
  ⟨classifyFourTile_sound, classifyFourTile_complete⟩

example : classifyFourTile (Tile.numberedTiles .Manzu [0, 1, 2, 4]) =
  some .tanki := by native_decide
example : classifyFourTile (Tile.numberedTiles .Manzu [0, 0, 0, 4]) =
  some .tanki := by native_decide
example : classifyFourTile
    (Tile.numberedTiles .Manzu [2, 3] ++ Tile.numberedTiles .Pinzu [4, 4]) =
    some .toitsuRyanmen := by
  native_decide
example : classifyFourTile
    (Tile.numberedTiles .Manzu [2, 4] ++ Tile.numberedTiles .Pinzu [4, 4]) =
    some .toitsuKanchan := by
  native_decide
example : classifyFourTile
    (Tile.numberedTiles .Manzu [0, 1] ++ Tile.numberedTiles .Pinzu [4, 4]) =
    some .toitsuPenchan := by
  native_decide
example : classifyFourTile
    (Tile.numberedTiles .Manzu [0, 0] ++ Tile.numberedTiles .Pinzu [1, 1]) =
    some .shanpon := by
  native_decide
example : classifyFourTile (Tile.numberedTiles .Manzu [0, 1, 2, 3]) = some .nobetan := by
  native_decide
example : classifyFourTile (Tile.numberedTiles .Manzu [1, 1, 1, 2]) =
    some .kuttsukiRyanmen := by native_decide
example : classifyFourTile (Tile.numberedTiles .Manzu [0, 0, 0, 2]) =
    some .kuttsukiKanchan := by native_decide
example : classifyFourTile (Tile.numberedTiles .Manzu [0, 0, 0, 1]) =
    some .kuttsukiPenchan := by native_decide

end FourTileAnalysis
