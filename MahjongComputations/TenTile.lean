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
open MahjongComputations

/-- Aggregated exhaustive report data for ten-tile shapes. -/
structure TenTileSummary where
  allTenTileShapes : Nat
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

private def emptySummary : TenTileSummary :=
  { allTenTileShapes := 0
    enumeratedDerivations := 0
    tenpaiReports := 0
    reducibleReports := 0
    irreducibleReports := 0
    waitCoreCacheHits := 0
    waitCoreCacheMisses := 0
    waitCoreCacheEntries := 0
    irreducibleGroups := []
    waitTileCountDistribution := [] }

private def allTenTileShapeCount (_ : Unit) : Nat :=
  countLegalTileMultisetsOfLength 10 Tile.all

private structure ComputationState where
  summary : TenTileSummary
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

/-- Exhaustive ten-tile aggregate summary with optional sharding. -/
def summaryWithShard (shardIndex : Nat := 0) (numShards : Nat := 1) : TenTileSummary :=
  let generated := canonicalWaitCompletionGroups 3
  let filtered := generated.groups.filter fun group =>
    (tileMultisetKey group.tiles) % numShards == shardIndex
  let computed :=
    filtered.foldl (fun state report => addShapeReport report state)
      { summary := emptySummary, waitCoreCache := emptyWaitCoreCache }
  { computed.summary with
    allTenTileShapes := allTenTileShapeCount ()
    enumeratedDerivations := generated.enumeratedDerivations
    waitCoreCacheHits := computed.waitCoreCache.hits
    waitCoreCacheMisses := computed.waitCoreCache.misses
    waitCoreCacheEntries := computed.waitCoreCache.values.size }

/-- Exhaustive ten-tile aggregate summary. -/
def summary (_ : Unit) : TenTileSummary :=
  summaryWithShard 0 1

end MahjongComputations.TenTile
