import Mahjong.DirectWaitGeneration
import Mahjong.WaitDecompositionCode
import MahjongComputations.Common
import MahjongComputations.Parallel
import MahjongComputations.ExternalWaitCompletion

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
open MahjongComputations

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

private def allThirteenTileShapeCount : Nat := 98521596000

private def addShapeReportShared (cache : SharedWaitCoreCache)
    (summary : ThirteenTileSummary) (report : WaitCompletionGroup) : IO ThirteenTileSummary := do
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

private def mergeSummary (first second : ThirteenTileSummary) : ThirteenTileSummary :=
  { first with
    tenpaiReports := first.tenpaiReports + second.tenpaiReports
    reducibleReports := first.reducibleReports + second.reducibleReports
    irreducibleReports := first.irreducibleReports + second.irreducibleReports
    irreducibleGroups := second.irreducibleGroups.foldl addCodeGroup first.irreducibleGroups
    waitTileCountDistribution :=
      second.waitTileCountDistribution.foldl addDistribution first.waitTileCountDistribution }

/-- Summary plus whether generation reused a completed external bucket set. -/
structure ThirteenTileRunResult where
  summary : ThirteenTileSummary
  generationReused : Bool

private def generateBuckets (workers : Nat) (workDirectory : System.FilePath)
    (bucketCount : Nat) : IO (List System.FilePath × Nat × Bool) := do
  if let some derivationCount ←
      ExternalWaitCompletion.readGenerationCheckpoint workDirectory 4 bucketCount then
    IO.eprintln s!"thirteen-tile: reusing {derivationCount} generated derivations"
    return (ExternalWaitCompletion.bucketPaths workDirectory bucketCount, derivationCount, true)
  ExternalWaitCompletion.clearGenerationCheckpoint workDirectory
  IO.eprintln s!"thirteen-tile: opening {bucketCount} buckets with {workers} generation workers"
  let generation ← ExternalWaitCompletion.withBucketSet workDirectory 4 bucketCount
    (action := fun buckets => do
      IO.eprintln "thirteen-tile: generating derivations"
      let counts ← parallelMapChunksIO workers Tile.all fun pairTiles =>
        foldCanonicalDirectWaitDerivationsForPairTilesM (n := 4) pairTiles 0
          fun count derivation => do
            buckets.append {
              tiles := DirectWaitGeneration.hand derivation
              completion := DirectWaitGeneration.completion derivation }
            pure (count + 1)
      return (buckets.paths, counts.sum))
  let (paths, derivationCount) := generation
  ExternalWaitCompletion.writeGenerationCheckpoint workDirectory 4 bucketCount derivationCount
  IO.eprintln s!"thirteen-tile: generated {derivationCount} derivations; checkpoint saved"
  return (paths, derivationCount, false)

/-- Generate or reuse external buckets, then classify them with a shared wait-core cache. -/
def summaryParallel (generationWorkers classificationWorkers : Nat)
    (workDirectory : System.FilePath) (bucketCount : Nat := 256) : IO ThirteenTileRunResult := do
  let (paths, enumeratedDerivations, generationReused) ←
    generateBuckets generationWorkers workDirectory bucketCount
  IO.eprintln s!"thirteen-tile: classifying {paths.length} buckets with {classificationWorkers} workers"
  let cache ← SharedWaitCoreCache.new
  let partials ← parallelMapChunksIO classificationWorkers paths fun workerPaths =>
    workerPaths.foldlM (init := emptySummary) fun summary path => do
      IO.eprintln s!"thirteen-tile: classifying {path}"
      let groups ← ExternalWaitCompletion.readGroups path 4
      groups.foldlM (addShapeReportShared cache) summary
  let computed := partials.foldl mergeSummary emptySummary
  let stats ← liftM cache.stats
  return {
    summary := { computed with
      allThirteenTileShapes := allThirteenTileShapeCount
      enumeratedDerivations
      waitCoreCacheHits := stats.hits
      waitCoreCacheMisses := stats.misses
      waitCoreCacheEntries := stats.entries }
    generationReused
  }

end MahjongComputations.ThirteenTile
