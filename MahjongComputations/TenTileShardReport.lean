import MahjongComputations.TenTile

/-!
# Ten-tile sharded report generator

Run individual shards with `lake build ten-tile-shard-report-gen -- --shard=i --num-shards=k`.
-/

namespace MahjongComputations.TenTileShardReport

open MahjongComputations.TenTile

private def newline : String := "\n"

private def reportBody (summary : TenTileSummary) (shardIdx : Nat) (numShards : Nat) : String :=
  String.intercalate newline <|
    [s!"# Ten-tile shard {shardIdx} of {numShards}",
     "",
     s!"shardIndex: {shardIdx}",
     s!"numShards: {numShards}",
     "",
     s!"allTenTileShapes: {summary.allTenTileShapes}",
     s!"enumeratedDerivations: {summary.enumeratedDerivations}",
     s!"tenpaiReports: {summary.tenpaiReports}",
     "",
     "## Reducibility",
     "",
     "### Reducible",
     s!"count: {summary.reducibleReports}",
     s!"waitCoreCacheHits: {summary.waitCoreCacheHits}",
     s!"waitCoreCacheMisses: {summary.waitCoreCacheMisses}",
     s!"waitCoreCacheEntries: {summary.waitCoreCacheEntries}",
     "",
     "### Irreducible",
     s!"count: {summary.irreducibleReports}",
     "",
     "#### Groups by waitDecompositionCodes",
     s!"groupCount: {summary.irreducibleGroups.length}",
     "waitDecompositionCodes\twaitDecompositionCodesKey\tcount\trepresentativeTiles\trepresentativeWaits"] ++
    summary.irreducibleGroups.map formatWaitDecompositionCodeGroup ++
    ["",
     "## Wait tile count distribution"] ++
    ((List.range Tile.count).map (fun index =>
      formatWaitTileCount summary.waitTileCountDistribution (index + 1))) ++
    [""]

private def reportText (elapsedMs : Nat) (body : String) : String :=
  String.intercalate newline [
    body,
    s!"calculationElapsedMs: {elapsedMs}",
    ""
  ]

def parseArgs (args : List String) : Option (Nat × Nat × String) := do
  let mut shardIndex : Option Nat := none
  let mut numShards : Option Nat := none
  let mut outputPath : Option String := none
  for arg in args do
    if arg.startsWith "--shard=" then
      let idx := arg.drop 8
      shardIndex := idx.toNat?
    else if arg.startsWith "--num-shards=" then
      let num := arg.drop 13
      numShards := num.toNat?
    else if !arg.startsWith "--" then
      outputPath := some arg
  (·, ·, ·) <$> shardIndex <*> numShards <*> outputPath

def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | none =>
      IO.eprintln "usage: ten-tile-shard-report-gen [--shard=i] [--num-shards=k] [output-file]"
      return 1
  | some (shardIndex, numShards, outputPath) =>
      let path : System.FilePath := outputPath
      if let some parent := path.parent then
        IO.FS.createDirAll parent
      let started ← IO.monoMsNow
      let computedSummary := summaryWithShard shardIndex numShards
      let body := reportBody computedSummary shardIndex numShards
      let bodySize := body.utf8ByteSize
      if bodySize == 0 then
        throw (IO.userError "empty ten-tile shard report body")
      let finished ← IO.monoMsNow
      IO.FS.writeFile path (reportText (finished - started) body)
      IO.println s!"wrote {path}"
      return 0

end MahjongComputations.TenTileShardReport

def main (args : List String) : IO UInt32 :=
  MahjongComputations.TenTileShardReport.run args
