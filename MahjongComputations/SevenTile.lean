import Mahjong.DirectWaitGeneration
import Mahjong.Wait.Analysis
import MahjongComputations.Common

/-!
# Seven-tile wait computation from direct derivations

This module enumerates valid two-mentsu derivations, projects them to seven-tile
hands, and folds the resulting tenpai hands into summary data.  The total number
of legal seven-tile multisets is counted separately, without materializing the
non-tenpai shapes.
-/

namespace MahjongComputations.SevenTile

open DirectWaitGeneration
open WaitCompletionFinder
open WaitDecompositionCode

/-- A summary group for irreducible seven-tile shapes sharing wait decomposition codes. -/
structure WaitDecompositionCodeGroup where
  codes : List Nat
  count : Nat
  representativeTiles : List Tile
  representativeWaits : List Tile
deriving BEq, DecidableEq, Repr

/-- Aggregated exhaustive report data for seven-tile shapes. -/
structure SevenTileSummary where
  allSevenTileShapes : Nat
  enumeratedDerivations : Nat
  tenpaiReports : Nat
  reducibleReports : Nat
  irreducibleReports : Nat
  irreducibleGroups : List WaitDecompositionCodeGroup
  waitTileCountDistribution : List (Nat × Nat)
deriving BEq, DecidableEq, Repr

private def emptySummary : SevenTileSummary :=
  { allSevenTileShapes := 0
    enumeratedDerivations := 0
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

private def addWaitDecompositionCodeGroup
    (codes : List Nat) (tiles waits : List Tile) : List WaitDecompositionCodeGroup → List WaitDecompositionCodeGroup
  | [] => [{ codes, count := 1, representativeTiles := tiles, representativeWaits := waits }]
  | group :: rest =>
      if group.codes == codes then
        { group with count := group.count + 1 } :: rest
      else
        group :: addWaitDecompositionCodeGroup codes tiles waits rest

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

private structure DerivationEntry where
  key : Nat
  tiles : List Tile
  completion : WaitCompletion
deriving BEq, DecidableEq, Repr

private structure SevenTileShapeReport where
  key : Nat
  tiles : List Tile
  completions : List WaitCompletion
deriving BEq, DecidableEq, Repr

private def derivationEntry (derivation : WaitDerivation 2) : DerivationEntry :=
  let tiles := hand derivation
  { key := tileMultisetKey tiles
    tiles
    completion := completion derivation }

private def derivationEntryKeyLE (first second : DerivationEntry) : Bool :=
  decide (first.key ≤ second.key)

private def insertCompletion (completion : WaitCompletion) (completions : List WaitCompletion) :
    List WaitCompletion :=
  if completions.contains completion then completions else completion :: completions

private def groupSortedDerivationEntry (groups : List SevenTileShapeReport) (entry : DerivationEntry) :
    List SevenTileShapeReport :=
  match groups with
  | [] => [{ key := entry.key, tiles := entry.tiles, completions := [entry.completion] }]
  | group :: rest =>
      if group.key == entry.key then
        { group with completions := insertCompletion entry.completion group.completions } :: rest
      else
        { key := entry.key, tiles := entry.tiles, completions := [entry.completion] } :: groups

private def sevenTileShapeReports (_ : Unit) : List SevenTileShapeReport :=
  (directWaitDerivations 2).map derivationEntry
    |>.mergeSort derivationEntryKeyLE
    |>.foldl groupSortedDerivationEntry []

private def waitsFromCompletions (completions : List WaitCompletion) : List Tile :=
  (completions.map fun completion => completion.wait).eraseDups

private def addShapeReport (report : SevenTileShapeReport) (summary : SevenTileSummary) :
    SevenTileSummary :=
  let completions := report.completions
  let waits := waitsFromCompletions completions
  let codes := waitDecompositionCodes completions
  let summary :=
    { summary with
      tenpaiReports := summary.tenpaiReports + 1
      waitTileCountDistribution := incrementAssoc waits.length summary.waitTileCountDistribution }
  if canReduceMentsuPreservingWaitCores report.tiles then
    { summary with reducibleReports := summary.reducibleReports + 1 }
  else
    { summary with
      irreducibleReports := summary.irreducibleReports + 1
      irreducibleGroups := addWaitDecompositionCodeGroup codes report.tiles waits summary.irreducibleGroups }

/-- Exhaustive seven-tile aggregate summary. -/
def summary (_ : Unit) : SevenTileSummary :=
  { (sevenTileShapeReports ()).foldl (fun summary report => addShapeReport report summary) emptySummary with
    allSevenTileShapes := allSevenTileShapeCount ()
    enumeratedDerivations := (directWaitDerivations 2).length }

end MahjongComputations.SevenTile
