import MahjongComputations.TenTile
import MahjongComputations.Parallel

/-!
# Ten-tile report generator

Run through Lake with `lake build tenTileReport`.
-/

namespace MahjongComputations.TenTileReport

open MahjongComputations.TenTile

private def newline : String := "\n"

private def reportBody (summary : TenTileSummary) : String :=
  String.intercalate newline <|
    ["# Ten-tile direct derivation wait report",
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

def run (args : List String) : IO UInt32 := do
  IO.eprintln "ten-tile: parsing arguments"
  let (workers, outputPath) ←
    MahjongComputations.parseWorkerArgs args "reports/ten-tile-report.txt"
  IO.eprintln s!"ten-tile: configured {workers} workers"
  let path : System.FilePath := outputPath
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  let started ← IO.monoMsNow
  let workDirectory : System.FilePath := ".lake/build/ten-tile-buckets"
  let computedSummary ← summaryParallel workers workDirectory
  let body := reportBody computedSummary
  let bodySize := body.utf8ByteSize
  if bodySize == 0 then
    throw (IO.userError "empty ten-tile report body")
  let finished ← IO.monoMsNow
  IO.FS.writeFile path (reportText (finished - started) body)
  IO.println s!"wrote {path}"
  return 0

end MahjongComputations.TenTileReport

def main (args : List String) : IO UInt32 :=
  MahjongComputations.TenTileReport.run args
