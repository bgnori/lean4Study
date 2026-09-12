import MahjongComputations.ThirteenTile
import MahjongComputations.Parallel

/-!
# Thirteen-tile report generator

Run through Lake with `lake build thirteenTileReport`.
-/

namespace MahjongComputations.ThirteenTileReport

open MahjongComputations.ThirteenTile

private structure Options where
  generationWorkers : Nat
  classificationWorkers : Nat
  bucketCount : Nat
  workDirectory : String
  outputPath : String

private def parsePositiveOption (name value : String) : IO Nat := do
  match value.toNat? with
  | some parsed =>
      if parsed == 0 then throw (IO.userError s!"{name} must be greater than zero")
      return parsed
  | none => throw (IO.userError s!"invalid value for {name}: {value}")

private def parseArgs (args : List String) : IO Options := do
  let availableWorkers ← MahjongComputations.availableWorkerCount
  let mut options : Options := {
    generationWorkers := availableWorkers
    classificationWorkers := min 8 availableWorkers
    bucketCount := 256
    workDirectory := ".lake/build/thirteen-tile-buckets"
    outputPath := "reports/thirteen-tile-report.txt"
  }
  for arg in args do
    if arg.startsWith "--generation-workers=" then
      let workers ← parsePositiveOption "--generation-workers" (arg.drop 21).toString
      options := { options with generationWorkers := workers }
    else if arg.startsWith "--classification-workers=" then
      let workers ← parsePositiveOption "--classification-workers" (arg.drop 25).toString
      options := { options with classificationWorkers := workers }
    else if arg.startsWith "--workers=" then
      let workers ← parsePositiveOption "--workers" (arg.drop 10).toString
      options := { options with generationWorkers := workers, classificationWorkers := workers }
    else if arg.startsWith "--buckets=" then
      let bucketCount ← parsePositiveOption "--buckets" (arg.drop 10).toString
      options := { options with bucketCount }
    else if arg.startsWith "--work-dir=" then
      options := { options with workDirectory := (arg.drop 11).toString }
    else if arg.startsWith "workers=" then
      throw (IO.userError s!"invalid worker option: {arg}; use --{arg}")
    else if arg.startsWith "--" then
      throw (IO.userError s!"unknown option: {arg}")
    else
      options := { options with outputPath := arg }
  return options

private def newline : String := "\n"

private def reportBody (options : Options) (result : ThirteenTileRunResult) : String :=
  let summary := result.summary
  String.intercalate newline <|
    ["# Thirteen-tile direct derivation wait report",
     "",
     s!"generationWorkers: {options.generationWorkers}",
     s!"classificationWorkers: {options.classificationWorkers}",
     s!"bucketCount: {options.bucketCount}",
     s!"generationReused: {result.generationReused}",
     "",
     s!"allThirteenTileShapes: {summary.allThirteenTileShapes}",
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
  let options ← parseArgs args
  let path : System.FilePath := options.outputPath
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  let started ← IO.monoMsNow
  let result ← summaryParallel options.generationWorkers options.classificationWorkers
    options.workDirectory options.bucketCount
  let body := reportBody options result
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
