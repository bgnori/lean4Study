import Mahjong.DirectWaitGeneration
import Mahjong.WaitDecompositionCode
import MahjongComputations.Common

/-!
# Ten-tile wait computation from direct derivations

This module enumerates valid three-mentsu derivations, projects them to ten-tile
hands, and folds the resulting tenpai hands into summary data.  The total number
of legal ten-tile multisets is counted separately, without materializing the
non-tenpai shapes.
-/

namespace MahjongComputations.TenTile

open DirectWaitGeneration
open WaitCompletionFinder
open WaitDecompositionCode

/-- Aggregated exhaustive report data for ten-tile shapes. -/
structure TenTileSummary where
  allTenTileShapes : Nat
  enumeratedDerivations : Nat
  tenpaiReports : Nat
  reducibleReports : Nat
  irreducibleReports : Nat
  irreducibleGroups : List WaitDecompositionCodeGroup
  waitTileCountDistribution : List (Nat × Nat)
deriving BEq, DecidableEq, Repr

private def emptySummary : TenTileSummary :=
  { allTenTileShapes := 0
    enumeratedDerivations := 0
    tenpaiReports := 0
    reducibleReports := 0
    irreducibleReports := 0
    irreducibleGroups := []
    waitTileCountDistribution := [] }

private def allTenTileShapeCount (_ : Unit) : Nat :=
  countLegalTileMultisetsOfLength 10 Tile.all

private def addShapeReport (report : WaitCompletionGroup) (summary : TenTileSummary) :
    TenTileSummary :=
  let completions := report.completions
  let waits := waitsFromCompletions completions
  let codes := waitDecompositionCodes completions
  let summary :=
    { summary with
      tenpaiReports := summary.tenpaiReports + 1
      waitTileCountDistribution := incrementCount waits.length summary.waitTileCountDistribution }
  if canReduceMentsuPreservingWaitCoresGivenCompletions report.tiles completions then
    { summary with reducibleReports := summary.reducibleReports + 1 }
  else
    { summary with
      irreducibleReports := summary.irreducibleReports + 1
      irreducibleGroups := addWaitDecompositionCodeGroup codes report.tiles waits summary.irreducibleGroups }

/-- Exhaustive ten-tile aggregate summary. -/
def summary (_ : Unit) : TenTileSummary :=
  let generated := canonicalWaitCompletionGroups 3
  let computedSummary :=
    generated.groups.foldl (fun summary report => addShapeReport report summary) emptySummary
  { computedSummary with
    allTenTileShapes := allTenTileShapeCount ()
    enumeratedDerivations := generated.enumeratedDerivations }

end MahjongComputations.TenTile
