import Mahjong.Wait.Analysis

/-!
# Exhaustive seven-tile wait computation

This module enumerates legal seven-tile multisets and folds them directly into
summary data, avoiding materializing all shapes at once.
-/

namespace MahjongComputations.SevenTile

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
  tenpaiReports : Nat
  reducibleReports : Nat
  irreducibleReports : Nat
  irreducibleGroups : List WaitReadingCodeGroup
  waitTileCountDistribution : List (Nat × Nat)
deriving BEq, DecidableEq, Repr

private def emptySummary : SevenTileSummary :=
  { allSevenTileShapes := 0
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

private def foldLegalTileMultisetsOfLength {α : Type}
    (length : Nat) (step : List Tile → α → α) (init : α) : α :=
  let rec go (remaining : Nat) (tiles : List Tile) (selectedTiles : List Tile) (acc : α) : α :=
    match tiles with
    | [] =>
        if remaining == 0 then
          step selectedTiles.reverse acc
        else
          acc
    | tile :: rest =>
        (List.range (Nat.min copiesPerTile remaining + 1)).foldl
          (fun acc copies =>
            go (remaining - copies) rest (List.replicate copies tile ++ selectedTiles) acc)
          acc
  go length Tile.all [] init

private def canReduceMentsuWithCompletionCount (tiles : List Tile) (completionCount : Nat) : Bool :=
  1 < tiles.length &&
    (mentsuReductions tiles).any (fun remaining =>
      let remainingCompletions := findWaitCompletions remaining
      !remainingCompletions.isEmpty && remainingCompletions.length == completionCount)

private def waitsFromCompletions (completions : List WaitCompletion) : List Tile :=
  (completions.map fun completion => completion.wait).eraseDups

private def addShape (tiles : List Tile) (summary : SevenTileSummary) : SevenTileSummary :=
  let summary := { summary with allSevenTileShapes := summary.allSevenTileShapes + 1 }
  let completions := findWaitCompletions tiles
  if completions.isEmpty then
    summary
  else
    let waits := waitsFromCompletions completions
    let codes := abstractWaitReadingCode completions
    let summary :=
      { summary with
        tenpaiReports := summary.tenpaiReports + 1
        waitTileCountDistribution := incrementAssoc waits.length summary.waitTileCountDistribution }
    if canReduceMentsuWithCompletionCount tiles completions.length then
      { summary with reducibleReports := summary.reducibleReports + 1 }
    else
      { summary with
        irreducibleReports := summary.irreducibleReports + 1
        irreducibleGroups := addWaitReadingCodeGroup codes tiles waits summary.irreducibleGroups }

/-- Exhaustive seven-tile aggregate summary. -/
def summary : SevenTileSummary :=
  foldLegalTileMultisetsOfLength 7 addShape emptySummary

end MahjongComputations.SevenTile
