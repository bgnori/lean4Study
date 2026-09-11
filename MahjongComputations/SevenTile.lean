import Mahjong.DirectWaitGeneration
import Mahjong.WaitDecompositionCode
import MahjongComputations.Common

/-!
# Seven-tile wait computation from direct derivations

This module enumerates valid two-mentsu derivations, projects them to seven-tile
hands, and folds the resulting tenpai hands into summary data.  The total number
of legal seven-tile multisets is counted separately, without materializing the
non-tenpai shapes.
-/

namespace MahjongComputations.SevenTile

open DirectWaitGeneration
open WaitCompletionFinder
open WaitDecompositionCode

/-- Aggregated exhaustive report data for seven-tile shapes. -/
structure SevenTileSummary where
  allSevenTileShapes : Nat
  enumeratedDerivations : Nat
  tenpaiReports : Nat
  reducibleReports : Nat
  irreducibleReports : Nat
  waitCoreCacheHits : Nat
  waitCoreCacheMisses : Nat
  waitCoreCacheEntries : Nat
  irreducibleGroups : List WaitDecompositionCodeGroup
  waitTileCountDistribution : List (Nat × Nat)
deriving BEq, DecidableEq, Repr

private def emptySummary : SevenTileSummary :=
  { allSevenTileShapes := 0
    enumeratedDerivations := 0
    tenpaiReports := 0
    reducibleReports := 0
    irreducibleReports := 0
    waitCoreCacheHits := 0
    waitCoreCacheMisses := 0
    waitCoreCacheEntries := 0
    irreducibleGroups := []
    waitTileCountDistribution := [] }

private def allSevenTileShapeCount (_ : Unit) : Nat :=
  countLegalTileMultisetsOfLength 7 Tile.all

private structure ComputationState where
  summary : SevenTileSummary
  waitCoreCache : WaitCoreCache

private def addShapeReport (report : WaitCompletionGroup) (state : ComputationState) :
    ComputationState :=
  let completions := report.completions
  let waits := waitsFromCompletions completions
  let codes := waitDecompositionCodes completions
  let (reducible, waitCoreCache) :=
    canReduceMentsuPreservingWaitCoresCached report.tiles completions state.waitCoreCache
  let summary :=
    { state.summary with
      tenpaiReports := state.summary.tenpaiReports + 1
      waitTileCountDistribution :=
        incrementCount waits.length state.summary.waitTileCountDistribution }
  let summary := if reducible then
    { summary with reducibleReports := summary.reducibleReports + 1 }
  else
    { summary with
      irreducibleReports := summary.irreducibleReports + 1
      irreducibleGroups := addWaitDecompositionCodeGroup codes report.tiles waits summary.irreducibleGroups }
  { summary, waitCoreCache }

/-- Exhaustive seven-tile aggregate summary. -/
def summary (_ : Unit) : SevenTileSummary :=
  let generated := canonicalWaitCompletionGroups 2
  let computed :=
    generated.groups.foldl (fun state report => addShapeReport report state)
      { summary := emptySummary, waitCoreCache := emptyWaitCoreCache }
  { computed.summary with
    allSevenTileShapes := allSevenTileShapeCount ()
    enumeratedDerivations := generated.enumeratedDerivations
    waitCoreCacheHits := computed.waitCoreCache.hits
    waitCoreCacheMisses := computed.waitCoreCache.misses
    waitCoreCacheEntries := computed.waitCoreCache.values.size }

example : countLegalTileMultisetsOfLength 7 Tile.all = 18623330 := by
  native_decide

end MahjongComputations.SevenTile
