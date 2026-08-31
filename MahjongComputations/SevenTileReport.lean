import MahjongComputations.SevenTile

/-!
# Seven-tile report generator

Run through Lake with `lake build sevenTileReport`.
-/

namespace MahjongComputations.SevenTileReport

open MahjongComputations.SevenTile

private def newline : String := "\n"

private def formatNumberedGroup (tiles : List Tile) (suit : Suit) (suffix : String) : String :=
  let digits := (List.ofFn fun rank : Rank => rank).flatMap fun rank =>
    List.replicate (tiles.count (.numbered suit rank)) (toString (rank.val + 1))
  if digits.isEmpty then "" else String.join digits ++ suffix

private def formatHonorGroup (tiles : List Tile) : String :=
  let digits := Honor.all.flatMap fun honor =>
    List.replicate (tiles.count (.honor honor)) (toString (honor.orderKey + 1))
  if digits.isEmpty then "" else String.join digits ++ "z"

private def formatTiles (tiles : List Tile) : String :=
  String.join <| [
    formatNumberedGroup tiles .Manzu "m",
    formatNumberedGroup tiles .Pinzu "p",
    formatNumberedGroup tiles .Souzu "s",
    formatHonorGroup tiles
  ].filter fun group => !group.isEmpty

private def waitReadingCodeGroupLine (group : WaitReadingCodeGroup) : String :=
  String.intercalate "\t" [
    toString group.codes,
    toString group.count,
    formatTiles group.representativeTiles,
    formatTiles group.representativeWaits
  ]

private def waitCountLine (distribution : List (Nat × Nat)) (count : Nat) : String :=
  s!"{count} wait tile kinds: {((distribution.find? fun entry => entry.1 == count).map Prod.snd).getD 0}"

private def reportBody (summary : SevenTileSummary) : String :=
  String.intercalate newline <|
    ["# Seven-tile direct Reading wait report",
     "",
     s!"allSevenTileShapes: {summary.allSevenTileShapes}",
     s!"enumeratedReadings: {summary.enumeratedReadings}",
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
     "#### Groups by waitReadingCodes",
     "waitReadingCodes\tcount\trepresentativeTiles\trepresentativeWaits"] ++
    summary.irreducibleGroups.map waitReadingCodeGroupLine ++
    ["",
     "## Wait tile count distribution"] ++
    ((List.range Tile.count).map (fun index => waitCountLine summary.waitTileCountDistribution (index + 1))) ++
    [""]

private def reportText (elapsedMs : Nat) (body : String) : String :=
  String.intercalate newline [
    body,
    s!"calculationElapsedMs: {elapsedMs}",
    ""
  ]

def run (args : List String) : IO UInt32 := do
  let outputPath := args.head?.getD "reports/seven-tile-report.txt"
  let path : System.FilePath := outputPath
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  let started ← IO.monoMsNow
  let computedSummary := summary ()
  let body := reportBody computedSummary
  let bodySize := body.utf8ByteSize
  if bodySize == 0 then
    throw (IO.userError "empty seven-tile report body")
  let finished ← IO.monoMsNow
  IO.FS.writeFile path (reportText (finished - started) body)
  IO.println s!"wrote {path}"
  return 0

end MahjongComputations.SevenTileReport

def main (args : List String) : IO UInt32 :=
  MahjongComputations.SevenTileReport.run args
