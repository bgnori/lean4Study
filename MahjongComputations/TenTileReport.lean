import MahjongComputations.TenTile

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
    s!"waitCoreCacheEvictions: {summary.waitCoreCacheEvictions}",
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
  let maxEntries := args.find? (·.startsWith "--max-entries=")
    |>.bind (fun arg => (arg.drop 14).toNat?) |>.getD 0
  let evictionPercent := args.find? (·.startsWith "--eviction-percent=")
    |>.bind (fun arg => (arg.drop 19).toNat?) |>.getD 0
  let outputPath := args.find? (fun arg => !arg.startsWith "--")
    |>.getD "reports/ten-tile-report.txt"
  let path : System.FilePath := outputPath
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  let started ← IO.monoMsNow
  let computedSummary := summaryWithCache 0 1 maxEntries evictionPercent
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
