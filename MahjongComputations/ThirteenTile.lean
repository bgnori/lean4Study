import Mahjong.DirectWaitGeneration
import Mahjong.WaitDecompositionCode
import MahjongComputations.Common

/-!
# Thirteen-tile wait computation from direct derivations

This module enumerates valid four-mentsu derivations, projects them to standard
thirteen-tile hands, and folds the resulting tenpai hands into summary data.  The
total number of legal thirteen-tile multisets is counted separately, without
materializing the non-tenpai shapes.
-/

namespace MahjongComputations.ThirteenTile

open DirectWaitGeneration
open WaitCompletionFinder
open WaitDecompositionCode

/-- Aggregated exhaustive report data for thirteen-tile shapes. -/
structure ThirteenTileSummary where
  allThirteenTileShapes : Nat
  enumeratedDerivations : Nat
  tenpaiReports : Nat
  reducibleReports : Nat
  irreducibleReports : Nat
  irreducibleGroups : List WaitDecompositionCodeGroup
  waitTileCountDistribution : List (Nat × Nat)
deriving BEq, DecidableEq, Repr

private def emptySummary : ThirteenTileSummary :=
  { allThirteenTileShapes := 0
    enumeratedDerivations := 0
    tenpaiReports := 0
    reducibleReports := 0
    irreducibleReports := 0
    irreducibleGroups := []
    waitTileCountDistribution := [] }

private def allThirteenTileShapeCount (_ : Unit) : Nat :=
  countLegalTileMultisetsOfLength 13 Tile.all

private def thirteenTileShapeReports
    (derivations : List (DirectWaitGeneration.WaitDerivation 4)) : List WaitCompletionGroup :=
  groupWaitDerivations derivations

private def addShapeReport (report : WaitCompletionGroup) (summary : ThirteenTileSummary) :
    ThirteenTileSummary :=
  let completions := report.completions
  let waits := waitsFromCompletions completions
  let codes := waitDecompositionCodes completions
  let summary :=
    { summary with
      tenpaiReports := summary.tenpaiReports + 1
      waitTileCountDistribution := incrementCount waits.length summary.waitTileCountDistribution }
  if canReduceMentsuPreservingWaitCores report.tiles then
    { summary with reducibleReports := summary.reducibleReports + 1 }
  else
    { summary with
      irreducibleReports := summary.irreducibleReports + 1
      irreducibleGroups := addWaitDecompositionCodeGroup codes report.tiles waits summary.irreducibleGroups }

/-- Exhaustive thirteen-tile aggregate summary. -/
def summary (_ : Unit) : ThirteenTileSummary :=
  let derivations := directWaitDerivations 4
  let shapeReports := thirteenTileShapeReports derivations
  let computedSummary :=
    shapeReports.foldl (fun summary report => addShapeReport report summary) emptySummary
  { computedSummary with
    allThirteenTileShapes := allThirteenTileShapeCount ()
    enumeratedDerivations := derivations.length }

end MahjongComputations.ThirteenTile
