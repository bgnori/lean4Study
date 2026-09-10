import MahjongComputations.ThirteenTile

/-!
# Thirteen-tile report generator

Run through Lake with `lake build thirteenTileReport`.
-/

namespace MahjongComputations.ThirteenTileReport

open MahjongComputations.ThirteenTile

private def newline : String := "\n"

private def reportBody (summary : ThirteenTileSummary) : String :=
  String.intercalate newline <|
    ["# Thirteen-tile direct derivation wait report",
     "",
     s!"allThirteenTileShapes: {summary.allThirteenTileShapes}",
    s!"enumeratedDerivations: {summary.enumeratedDerivations}",
     s!"tenpaiReports: {summary.tenpaiReports}",
     "",
     "## Reducibility",
     "",
     "### Reducible",
     s!"count: {summary.reducibleReports}",
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
  let outputPath := args.head?.getD "reports/thirteen-tile-report.txt"
  let path : System.FilePath := outputPath
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  let started ← IO.monoMsNow
  let computedSummary := summary ()
  let body := reportBody computedSummary
  let bodySize := body.utf8ByteSize
  if bodySize == 0 then
    throw (IO.userError "empty thirteen-tile report body")
  let finished ← IO.monoMsNow
  IO.FS.writeFile path (reportText (finished - started) body)
  IO.println s!"wrote {path}"
  return 0

end MahjongComputations.ThirteenTileReport

def main (args : List String) : IO UInt32 :=
  MahjongComputations.ThirteenTileReport.run args
