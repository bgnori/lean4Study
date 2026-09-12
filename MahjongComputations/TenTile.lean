import Mahjong.DirectWaitGeneration
import Mahjong.WaitDecompositionCode
import MahjongComputations.Common
import MahjongComputations.Parallel
import MahjongComputations.ExternalWaitCompletion

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

private def allTenTileShapeCount : Nat := 1900269316

private def addShapeReportShared (cache : SharedWaitCoreCache)
    (summary : TenTileSummary) (report : WaitCompletionGroup) : IO TenTileSummary := do
  let completions := report.completions
  let waits := waitsFromCompletions completions
  let codes := waitDecompositionCodes completions
  let reducible ← liftM <| canReduceMentsuPreservingWaitCoresShared report.tiles completions cache
  let summary :=
    { summary with
      tenpaiReports := summary.tenpaiReports + 1
      waitTileCountDistribution := incrementCount waits.length summary.waitTileCountDistribution }
  if reducible then
    return { summary with reducibleReports := summary.reducibleReports + 1 }
  else
    return { summary with
      irreducibleReports := summary.irreducibleReports + 1
      irreducibleGroups := addWaitDecompositionCodeGroup codes report.tiles waits summary.irreducibleGroups }

private def addCodeGroup
    (groups : List WaitDecompositionCodeGroup) (addition : WaitDecompositionCodeGroup) :
    List WaitDecompositionCodeGroup :=
  match groups with
  | [] => [addition]
  | group :: rest =>
      if group.codes == addition.codes then
        { group with count := group.count + addition.count } :: rest
      else
        group :: addCodeGroup rest addition

private def addDistribution
    (counts : List (Nat × Nat)) (addition : Nat × Nat) : List (Nat × Nat) :=
  match counts with
  | [] => [addition]
  | count :: rest =>
      if count.1 == addition.1 then
        (count.1, count.2 + addition.2) :: rest
      else
        count :: addDistribution rest addition

private def mergeSummary (first second : TenTileSummary) : TenTileSummary :=
  { first with
    tenpaiReports := first.tenpaiReports + second.tenpaiReports
    reducibleReports := first.reducibleReports + second.reducibleReports
    irreducibleReports := first.irreducibleReports + second.irreducibleReports
    irreducibleGroups := second.irreducibleGroups.foldl addCodeGroup first.irreducibleGroups
    waitTileCountDistribution :=
      second.waitTileCountDistribution.foldl addDistribution first.waitTileCountDistribution }

/-- Generate and classify ten-tile derivations through bounded external hash buckets. -/
def summaryParallel (workers : Nat) (workDirectory : System.FilePath)
    (bucketCount : Nat := 64) : IO TenTileSummary := do
  IO.eprintln s!"ten-tile: opening {bucketCount} buckets with {workers} workers"
  let generation ← ExternalWaitCompletion.withBucketSet workDirectory 3 bucketCount
    (action := fun buckets => do
      IO.eprintln "ten-tile: generating derivations"
      let counts ← parallelMapChunksIO workers Tile.all fun pairTiles =>
        foldCanonicalDirectWaitDerivationsForPairTilesM (n := 3) pairTiles 0
          fun count derivation => do
            buckets.append {
              tiles := DirectWaitGeneration.hand derivation
              completion := DirectWaitGeneration.completion derivation }
            pure (count + 1)
      return (buckets.paths, counts.sum))
  let (paths, enumeratedDerivations) := generation
  IO.eprintln s!"ten-tile: generated {enumeratedDerivations} derivations; classifying buckets"
  let cache ← SharedWaitCoreCache.new
  let partials ← parallelMapChunksIO workers paths fun workerPaths =>
    workerPaths.foldlM (init := emptySummary) fun summary path => do
      let groups ← ExternalWaitCompletion.readGroups path 3
      groups.foldlM (addShapeReportShared cache) summary
  let computed := partials.foldl mergeSummary emptySummary
  let stats ← liftM cache.stats
  return { computed with
    allTenTileShapes := allTenTileShapeCount
    enumeratedDerivations
    waitCoreCacheHits := stats.hits
    waitCoreCacheMisses := stats.misses
    waitCoreCacheEntries := stats.entries }

end MahjongComputations.TenTile
