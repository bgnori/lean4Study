import Mahjong.FourTileWait.Specification
import Mahjong.DecompositionCode

/-!
# 4枚待ち分類の解析器

通常形の和了分解から `FourTileProfile` を観測し、純粋な仕様
`FourTileSpecification.Classifies` を決定する。
-/

namespace FourTileAnalysis

open DecompositionCode

/-- 形部品列を4枚待ち仕様の基本形へ変換する。 -/
def fourTileProfileOfComponents : List DecompositionComponent → Option FourTileProfile
  | [.tanki, .shuntsu] => some .tankiShuntsu
  | [.tanki, .koutsu] => some .tankiKoutsu
  | [.toitsu, .ryanmen] => some .toitsuRyanmen
  | [.toitsu, .kanchan] => some .toitsuKanchan
  | [.toitsu, .penchan] => some .toitsuPenchan
  | [.toitsu, .toitsu] => some .shanpon
  | _ => none

/-- 通常形の和了分解から得られる4枚基本形の正規化済み観測列。 -/
def observedFourTileProfiles (tiles : List Tile) : List FourTileProfile :=
  (findAbstractDecompositionExtractions tiles).filterMap fun extraction =>
    fourTileProfileOfComponents extraction.components

/-- 純粋な分類仕様を実行する、基本形列上の決定手続き。 -/
def classifyFourTileProfiles (profiles : List FourTileProfile) : Option FourTileWaitKind :=
  FourTileSpecification.expectedKind profiles

/-- 基本形上の解析器は宣言的な分類仕様に対して健全かつ完全である。 -/
theorem classifyFourTileProfiles_iff (profiles : List FourTileProfile)
    (kind : FourTileWaitKind) :
    classifyFourTileProfiles profiles = some kind ↔
      FourTileSpecification.Classifies profiles kind := by
  rfl

/-- 4枚牌列に名前付き分類を与える解析器。 -/
def classifyFourTile (tiles : List Tile) : Option FourTileWaitKind :=
  if tiles.length = fourTileHandSize then
    classifyFourTileProfiles (observedFourTileProfiles tiles)
  else
    none

/-- 牌列が名前付き4枚分類の仕様を満たすこと。 -/
def HasFourTileKind (tiles : List Tile) (kind : FourTileWaitKind) : Prop :=
  tiles.length = fourTileHandSize ∧
    FourTileSpecification.Classifies (observedFourTileProfiles tiles) kind

/-- `classifyFourTile` の健全性。 -/
theorem classifyFourTile_sound {tiles : List Tile} {kind : FourTileWaitKind}
    (classified : classifyFourTile tiles = some kind) :
    HasFourTileKind tiles kind := by
  unfold classifyFourTile at classified
  unfold HasFourTileKind
  split at classified <;> simp_all [classifyFourTileProfiles_iff]

/-- `classifyFourTile` の完全性。 -/
theorem classifyFourTile_complete {tiles : List Tile} {kind : FourTileWaitKind}
    (specified : HasFourTileKind tiles kind) :
    classifyFourTile tiles = some kind := by
  rcases specified with ⟨length, classified⟩
  unfold classifyFourTile
  simp [length, classifyFourTileProfiles_iff, classified]

/-- 健全性と完全性をまとめた特徴付け。 -/
theorem classifyFourTile_iff (tiles : List Tile) (kind : FourTileWaitKind) :
    classifyFourTile tiles = some kind ↔ HasFourTileKind tiles kind :=
  ⟨classifyFourTile_sound, classifyFourTile_complete⟩

example : classifyFourTile (Tile.numberedTiles .Manzu [0, 1, 2, 4]) =
    some .tankiShuntsu := by native_decide
example : classifyFourTile (Tile.numberedTiles .Manzu [0, 0, 0, 4]) =
    some .tankiKoutsu := by native_decide
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
