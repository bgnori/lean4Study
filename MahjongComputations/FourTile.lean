import Mahjong.DirectWaitReading
import Mahjong.Wait.Analysis

/-!
# Exhaustive four-tile wait computation

This module is intentionally outside the `Mahjong` library.  It enumerates all
legal four-tile multisets and computes the wait information that is useful for
studying one-mentsu standard-form tenpai shapes.
-/

namespace MahjongComputations.FourTile

open DirectWaitReading
open WaitReadingCode
open WaitCompletionFinder

/-- A computed summary for one four-tile shape. -/
structure FourTileShapeReport where
  tiles : List Tile
  waits : List Tile
  kind : Option WaitKind
  candidateKinds : List WaitKind
  reducibility : Option WaitReducibility
  waitReadingCodes : List Nat
deriving BEq, DecidableEq, Repr

private def legalTileMultisetsOfLength (length : Nat) : List Tile → List (List Tile)
  | [] =>
      if length == 0 then [[]] else []
  | tile :: rest =>
      (List.range (Nat.min copiesPerTile length + 1)).flatMap fun copies =>
        (legalTileMultisetsOfLength (length - copies) rest).map fun tail =>
          List.replicate copies tile ++ tail
termination_by tiles => tiles.length

/-- All legal four-tile shapes as sorted tile-type multisets. -/
def allFourTileShapes : List (List Tile) :=
  legalTileMultisetsOfLength 4 Tile.all

/-- Computed wait report for a four-tile shape, including non-tenpai shapes. -/
def report (tiles : List Tile) : FourTileShapeReport :=
  { tiles
    waits := waitingTiles tiles
    kind := WaitAnalysis.classifyWait tiles
    candidateKinds := WaitAnalysis.candidateWaitKinds tiles
    reducibility := WaitAnalysis.determineReducibility tiles
    waitReadingCodes := findAbstractWaitReadingCode tiles }

/-- Exhaustive four-tile tenpai reports. -/
def tenpaiReports : List FourTileShapeReport :=
  allFourTileShapes.filterMap fun tiles =>
    let waits := waitingTiles tiles
    if waits.isEmpty then
      none
    else
      some
        { tiles
          waits
          kind := WaitAnalysis.classifyWait tiles
          candidateKinds := WaitAnalysis.candidateWaitKinds tiles
          reducibility := WaitAnalysis.determineReducibility tiles
          waitReadingCodes := findAbstractWaitReadingCode tiles }

private def tileMultisetKey (tiles : List Tile) : Nat :=
  Tile.all.foldl (fun key tile => key * (copiesPerTile + 1) + tiles.count tile) 0

private structure DirectReadingEntry where
  key : Nat
  tiles : List Tile
  completion : WaitCompletion
deriving BEq, DecidableEq, Repr

private structure DirectFourTileShapeReport where
  key : Nat
  tiles : List Tile
  completions : List WaitCompletion
deriving BEq, DecidableEq, Repr

private def directReadingEntry (reading : Reading 1) : DirectReadingEntry :=
  let tiles := hand reading
  { key := tileMultisetKey tiles
    tiles
    completion := completion reading }

private def directReadingEntryKeyLE (first second : DirectReadingEntry) : Bool :=
  decide (first.key ≤ second.key)

private def insertCompletion (completion : WaitCompletion) (completions : List WaitCompletion) :
    List WaitCompletion :=
  if completions.contains completion then completions else completion :: completions

private def groupSortedDirectReadingEntry
    (groups : List DirectFourTileShapeReport) (entry : DirectReadingEntry) :
    List DirectFourTileShapeReport :=
  match groups with
  | [] => [{ key := entry.key, tiles := entry.tiles, completions := [entry.completion] }]
  | group :: _ =>
      if group.key == entry.key then
        { group with completions := insertCompletion entry.completion group.completions } :: groups.tail
      else
        { key := entry.key, tiles := entry.tiles, completions := [entry.completion] } :: groups

private def directFourTileShapeReports (_ : Unit) : List DirectFourTileShapeReport :=
  (directReadings 1).map directReadingEntry
    |>.mergeSort directReadingEntryKeyLE
    |>.foldl groupSortedDirectReadingEntry []

private def waitsFromCompletions (completions : List WaitCompletion) : List Tile :=
  (completions.map fun completion => completion.wait).eraseDups

private def waitProfilesFromCompletions (completions : List WaitCompletion) : List WaitProfile :=
  (abstractWaitReadings completions).flatMap fun reading =>
    WaitAnalysis.waitProfilesOfComponents reading.components

private def canReduceMentsuWithCompletionCount (tiles : List Tile) (completionCount : Nat) : Bool :=
  1 < tiles.length &&
    (mentsuReductions tiles).any (fun remaining =>
      let remainingCompletions := findWaitCompletions remaining
      !remainingCompletions.isEmpty && remainingCompletions.length == completionCount)

private def directReport (report : DirectFourTileShapeReport) : FourTileShapeReport :=
  let completions := report.completions
  let profiles := waitProfilesFromCompletions completions
  { tiles := report.tiles
    waits := waitsFromCompletions completions
    kind := WaitAnalysis.classifyWaitProfiles profiles
    candidateKinds := WaitAnalysis.candidateWaitKindsOfProfiles profiles
    reducibility :=
      some <| if canReduceMentsuWithCompletionCount report.tiles completions.length then
        .reducible
      else
        .irreducible
    waitReadingCodes := abstractWaitReadingCode completions }

/-- Number of normalized direct Readings enumerated for four-tile shapes. -/
def directReadingCount : Nat :=
  (directReadings 1).length

/-- Four-tile tenpai reports computed by projecting direct Readings and grouping equal hands. -/
def directReadingTenpaiReports : List FourTileShapeReport :=
  (directFourTileShapeReports ()).map directReport

/-- Exhaustive four-tile reports whose classified wait kind is `kind`. -/
def reportsOfKind (kind : WaitKind) : List FourTileShapeReport :=
  tenpaiReports.filter fun report => report.kind == some kind

/-- Count four-tile tenpai shapes by named wait kind. -/
def countsByKind : List (WaitKind × Nat) :=
  WaitKind.all.map fun kind => (kind, (reportsOfKind kind).length)

/-- Four-tile tenpai shapes that the classifier did not assign to a `WaitKind`. -/
def unclassifiedTenpaiReports : List FourTileShapeReport :=
  tenpaiReports.filter fun report => report.kind.isNone

/-- Four-tile tenpai shapes with more than one broad candidate wait kind. -/
def ambiguousReports : List FourTileShapeReport :=
  tenpaiReports.filter fun report => 1 < report.candidateKinds.length

/-- Irreducible four-tile tenpai shapes. -/
def irreducibleReports : List FourTileShapeReport :=
  tenpaiReports.filter fun report => report.reducibility == some .irreducible

example :
    (report (manzu [1, 1, 2, 3])).candidateKinds = [.tanki, .toitsuRyanmen] := by
  native_decide

example : allFourTileShapes.length = 66045 := by
  native_decide

end MahjongComputations.FourTile
