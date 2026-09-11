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
  waitCoreCacheHits : Nat
  waitCoreCacheMisses : Nat
  waitCoreCacheEntries : Nat
  irreducibleGroups : List WaitDecompositionCodeGroup
  waitTileCountDistribution : List (Nat × Nat)
deriving BEq, DecidableEq, Repr

private def emptySummary : ThirteenTileSummary :=
  { allThirteenTileShapes := 0
    enumeratedDerivations := 0
    tenpaiReports := 0
    reducibleReports := 0
    irreducibleReports := 0
    waitCoreCacheHits := 0
    waitCoreCacheMisses := 0
    waitCoreCacheEntries := 0
    irreducibleGroups := []
    waitTileCountDistribution := [] }

private def allThirteenTileShapeCount (_ : Unit) : Nat :=
  countLegalTileMultisetsOfLength 13 Tile.all

private structure ComputationState where
  summary : ThirteenTileSummary
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

/-- Exhaustive thirteen-tile aggregate summary. -/
def summary (_ : Unit) : ThirteenTileSummary :=
  let generated := canonicalWaitCompletionGroups 4
  let computed :=
    generated.groups.foldl (fun state report => addShapeReport report state)
      { summary := emptySummary, waitCoreCache := emptyWaitCoreCache }
  { computed.summary with
    allThirteenTileShapes := allThirteenTileShapeCount ()
    enumeratedDerivations := generated.enumeratedDerivations
    waitCoreCacheHits := computed.waitCoreCache.hits
    waitCoreCacheMisses := computed.waitCoreCache.misses
    waitCoreCacheEntries := computed.waitCoreCache.values.size }

end MahjongComputations.ThirteenTile
