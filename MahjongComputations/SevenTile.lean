import Mahjong.DirectWaitReading
import Mahjong.Wait.Analysis

/-!
# Seven-tile wait computation from direct Readings

This module enumerates valid two-mentsu Readings, projects them to seven-tile
hands, and folds the resulting tenpai hands into summary data.  The total number
of legal seven-tile multisets is counted separately, without materializing the
non-tenpai shapes.
-/

namespace MahjongComputations.SevenTile

open DirectWaitReading
open WaitCompletionFinder
open WaitReadingCode

/-- A summary group for irreducible seven-tile shapes sharing abstract wait-reading codes. -/
structure WaitReadingCodeGroup where
  codes : List Nat
  count : Nat
  representativeTiles : List Tile
  representativeWaits : List Tile
deriving BEq, DecidableEq, Repr

/-- Aggregated exhaustive report data for seven-tile shapes. -/
structure SevenTileSummary where
  allSevenTileShapes : Nat
  enumeratedReadings : Nat
  tenpaiReports : Nat
  reducibleReports : Nat
  irreducibleReports : Nat
  irreducibleGroups : List WaitReadingCodeGroup
  waitTileCountDistribution : List (Nat × Nat)
deriving BEq, DecidableEq, Repr

private def emptySummary : SevenTileSummary :=
  { allSevenTileShapes := 0
    enumeratedReadings := 0
    tenpaiReports := 0
    reducibleReports := 0
    irreducibleReports := 0
    irreducibleGroups := []
    waitTileCountDistribution := [] }

private def incrementAssoc (key : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(key, 1)]
  | entry :: rest =>
      if entry.1 == key then
        (entry.1, entry.2 + 1) :: rest
      else
        entry :: incrementAssoc key rest

private def addWaitReadingCodeGroup
    (codes : List Nat) (tiles waits : List Tile) : List WaitReadingCodeGroup → List WaitReadingCodeGroup
  | [] => [{ codes, count := 1, representativeTiles := tiles, representativeWaits := waits }]
  | group :: rest =>
      if group.codes == codes then
        { group with count := group.count + 1 } :: rest
      else
        group :: addWaitReadingCodeGroup codes tiles waits rest

private def countLegalTileMultisetsOfLength : Nat → List Tile → Nat
  | length, [] =>
      if length == 0 then 1 else 0
  | length, _ :: rest =>
      (List.range (Nat.min copiesPerTile length + 1)).foldl
        (fun total copies => total + countLegalTileMultisetsOfLength (length - copies) rest)
        0
termination_by _ tiles => tiles.length

private def allSevenTileShapeCount (_ : Unit) : Nat :=
  countLegalTileMultisetsOfLength 7 Tile.all

private def tileMultisetKey (tiles : List Tile) : Nat :=
  Tile.all.foldl (fun key tile => key * (copiesPerTile + 1) + tiles.count tile) 0

private structure ReadingEntry where
  key : Nat
  tiles : List Tile
  completion : WaitCompletion
deriving BEq, DecidableEq, Repr

private structure SevenTileShapeReport where
  key : Nat
  tiles : List Tile
  completions : List WaitCompletion
deriving BEq, DecidableEq, Repr

private def readingEntry (reading : Reading 2) : ReadingEntry :=
  let tiles := hand reading
  { key := tileMultisetKey tiles
    tiles
    completion := completion reading }

private def readingEntryKeyLE (first second : ReadingEntry) : Bool :=
  decide (first.key ≤ second.key)

private def insertCompletion (completion : WaitCompletion) (completions : List WaitCompletion) :
    List WaitCompletion :=
  if completions.contains completion then completions else completion :: completions

private def groupSortedReadingEntry (groups : List SevenTileShapeReport) (entry : ReadingEntry) :
    List SevenTileShapeReport :=
  match groups with
  | [] => [{ key := entry.key, tiles := entry.tiles, completions := [entry.completion] }]
  | group :: rest =>
      if group.key == entry.key then
        { group with completions := insertCompletion entry.completion group.completions } :: rest
      else
        { key := entry.key, tiles := entry.tiles, completions := [entry.completion] } :: groups

private def sevenTileShapeReports (_ : Unit) : List SevenTileShapeReport :=
  (directReadings 2).map readingEntry
    |>.mergeSort readingEntryKeyLE
    |>.foldl groupSortedReadingEntry []

private def canReduceMentsuWithCompletionCount (tiles : List Tile) (completionCount : Nat) : Bool :=
  1 < tiles.length &&
    (mentsuReductions tiles).any (fun remaining =>
      let remainingCompletions := findWaitCompletions remaining
      !remainingCompletions.isEmpty && remainingCompletions.length == completionCount)

private def waitsFromCompletions (completions : List WaitCompletion) : List Tile :=
  (completions.map fun completion => completion.wait).eraseDups

private def addShapeReport (report : SevenTileShapeReport) (summary : SevenTileSummary) :
    SevenTileSummary :=
  let completions := report.completions
  let waits := waitsFromCompletions completions
  let codes := abstractWaitReadingCode completions
  let summary :=
    { summary with
      tenpaiReports := summary.tenpaiReports + 1
      waitTileCountDistribution := incrementAssoc waits.length summary.waitTileCountDistribution }
  if canReduceMentsuWithCompletionCount report.tiles completions.length then
    { summary with reducibleReports := summary.reducibleReports + 1 }
  else
    { summary with
      irreducibleReports := summary.irreducibleReports + 1
      irreducibleGroups := addWaitReadingCodeGroup codes report.tiles waits summary.irreducibleGroups }

/-- Exhaustive seven-tile aggregate summary. -/
def summary (_ : Unit) : SevenTileSummary :=
  { (sevenTileShapeReports ()).foldl (fun summary report => addShapeReport report summary) emptySummary with
    allSevenTileShapes := allSevenTileShapeCount ()
    enumeratedReadings := (directReadings 2).length }

end MahjongComputations.SevenTile
