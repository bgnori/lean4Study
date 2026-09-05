import Mahjong.DirectWaitGeneration
import MahjongComputations.Common

/-!
# Exhaustive four-tile wait computation

This module is intentionally outside the `Mahjong` library.  It enumerates all
legal four-tile multisets and computes the wait information that is useful for
studying one-mentsu standard-form tenpai shapes.
-/

namespace MahjongComputations.FourTile

open DirectWaitGeneration
open WaitDecompositionCode
open WaitCompletionFinder

/-- A computed summary for one four-tile shape. -/
structure FourTileShapeReport where
  tiles : List Tile
  waits : List Tile
  reducibility : Option WaitReducibility
  waitDecompositionCodes : List Nat
deriving BEq, DecidableEq, Repr

private def legalTileMultisetsOfLength (length : Nat) : List Tile → List (List Tile)
  | [] =>
      if length == 0 then [[]] else []
  | tile :: rest =>
      (List.range (Nat.min copiesPerTile length + 1)).flatMap fun copies =>
        (legalTileMultisetsOfLength (length - copies) rest).map fun tail =>
          List.replicate copies tile ++ tail
termination_by tiles => tiles.length

/-- All legal four-tile shapes as sorted tile-type multisets. -/
def allFourTileShapes : List (List Tile) :=
  legalTileMultisetsOfLength 4 Tile.all

/-- Computed wait report for a four-tile shape, including non-tenpai shapes. -/
def report (tiles : List Tile) : FourTileShapeReport :=
  { tiles
    waits := waitingTiles tiles
    reducibility := determineReducibility tiles
    waitDecompositionCodes := findWaitDecompositionCodes tiles }

/-- Exhaustive four-tile tenpai reports. -/
def tenpaiReports : List FourTileShapeReport :=
  allFourTileShapes.filterMap fun tiles =>
    let waits := waitingTiles tiles
    if waits.isEmpty then
      none
    else
      some
        { tiles
          waits
          reducibility := determineReducibility tiles
          waitDecompositionCodes := findWaitDecompositionCodes tiles }

private structure DirectDerivationEntry where
  key : Nat
  tiles : List Tile
  completion : WaitCompletion
deriving BEq, DecidableEq, Repr

private structure DirectFourTileShapeReport where
  key : Nat
  tiles : List Tile
  completions : List WaitCompletion
deriving BEq, DecidableEq, Repr

private def directDerivationEntry (derivation : WaitDerivation 1) : DirectDerivationEntry :=
  let tiles := hand derivation
  { key := tileMultisetKey tiles
    tiles
    completion := completion derivation }

private def directDerivationEntryKeyLE (first second : DirectDerivationEntry) : Bool :=
  decide (first.key ≤ second.key)

private def insertCompletion (completion : WaitCompletion) (completions : List WaitCompletion) :
    List WaitCompletion :=
  if completions.contains completion then completions else completion :: completions

private def groupSortedDirectDerivationEntry
    (groups : List DirectFourTileShapeReport) (entry : DirectDerivationEntry) :
    List DirectFourTileShapeReport :=
  match groups with
  | [] => [{ key := entry.key, tiles := entry.tiles, completions := [entry.completion] }]
  | group :: _ =>
      if group.key == entry.key then
        { group with completions := insertCompletion entry.completion group.completions } :: groups.tail
      else
        { key := entry.key, tiles := entry.tiles, completions := [entry.completion] } :: groups

private def directFourTileShapeReports (_ : Unit) : List DirectFourTileShapeReport :=
  (directWaitDerivations 1).map directDerivationEntry
    |>.mergeSort directDerivationEntryKeyLE
    |>.foldl groupSortedDirectDerivationEntry []

private def waitsFromCompletions (completions : List WaitCompletion) : List Tile :=
  (completions.map fun completion => completion.wait).eraseDups

private def directReport (report : DirectFourTileShapeReport) : FourTileShapeReport :=
  let completions := report.completions
  { tiles := report.tiles
    waits := waitsFromCompletions completions
    reducibility :=
      some <| if canReduceMentsuPreservingWaitCores report.tiles then
        .reducible
      else
        .irreducible
    waitDecompositionCodes := waitDecompositionCodes completions }

/-- Number of normalized direct derivations enumerated for four-tile shapes. -/
def directDerivationCount : Nat :=
  (directWaitDerivations 1).length

/-- Four-tile tenpai reports computed by projecting direct derivations and grouping equal hands. -/
def directDerivationTenpaiReports : List FourTileShapeReport :=
  (directFourTileShapeReports ()).map directReport

/-- Irreducible four-tile tenpai shapes. -/
def irreducibleReports : List FourTileShapeReport :=
  tenpaiReports.filter fun report => report.reducibility == some .irreducible

example : allFourTileShapes.length = 66045 := by
  native_decide

end MahjongComputations.FourTile
