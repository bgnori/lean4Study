import MahjongComputations.FourTile

/-!
# Four-tile report generator

Run through Lake with `lake build fourTileReport`.
-/

namespace MahjongComputations.FourTileReport

open MahjongComputations.FourTile
open WaitDecompositionCode

private def newline : String := "\n"

private def reducibilityName : Option WaitReducibility → String
  | none => "none"
  | some .reducible => "reducible"
  | some .irreducible => "irreducible"

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

private def reportLine (report : FourTileShapeReport) : String :=
  String.intercalate "\t" [
    formatTiles report.tiles,
    formatTiles report.waits,
    reducibilityName report.reducibility,
    toString report.waitDecompositionCodes
  ]

private def reducibilityCount (reports : List FourTileShapeReport)
    (reducibility : WaitReducibility) : Nat :=
  (reports.filter fun report => report.reducibility == some reducibility).length

private def reportsByReducibility (reducibility : WaitReducibility) : List FourTileShapeReport :=
  directDerivationTenpaiReports.filter fun report => report.reducibility == some reducibility

private def waitCountLine (count : Nat) : String :=
  s!"{count} wait tile kinds: {(directDerivationTenpaiReports.filter fun report => report.waits.length == count).length}"

private def waitDecompositionCodeGroupLine (source : List FourTileShapeReport) (codes : List Nat) : String :=
  let group := source.filter fun report => report.waitDecompositionCodes == codes
  match group with
  | [] => ""
  | representative :: _ =>
      String.intercalate "\t" [
        toString codes,
        toString group.length,
        formatTiles representative.tiles,
        formatTiles representative.waits
      ]

private def reportText : String :=
  let irreducibleReports := reportsByReducibility .irreducible
  String.intercalate newline <|
    ["# Four-tile direct derivation wait report",
     "",
     s!"allFourTileShapes: {allFourTileShapes.length}",
    s!"enumeratedDerivations: {directDerivationCount}",
    s!"tenpaiReports: {directDerivationTenpaiReports.length}",
      "",
     "## Reducibility",
     "",
     "### Reducible",
     s!"count: {reducibilityCount tenpaiReports .reducible}",
     "",
     "### Irreducible",
     s!"count: {reducibilityCount tenpaiReports .irreducible}",
     "",
    "#### Groups by waitDecompositionCodes",
    "waitDecompositionCodes\tcount\trepresentativeTiles\trepresentativeWaits"] ++
    (irreducibleReports.map (·.waitDecompositionCodes)).eraseDups.map
      (waitDecompositionCodeGroupLine irreducibleReports) ++
    ["",
     "## Wait tile count distribution"] ++
    ([1, 2, 3, 4].map waitCountLine) ++
    ["",
     "## Tenpai reports",
    "tiles\twaits\treducibility\twaitDecompositionCodes"] ++
    directDerivationTenpaiReports.map reportLine ++
    [""]

def run (args : List String) : IO UInt32 := do
  let outputPath := args.head?.getD "reports/four-tile-direct-report.txt"
  let path : System.FilePath := outputPath
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path reportText
  IO.println s!"wrote {path}"
  return 0

end MahjongComputations.FourTileReport

def main (args : List String) : IO UInt32 :=
  MahjongComputations.FourTileReport.run args
