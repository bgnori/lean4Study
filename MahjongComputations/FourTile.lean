import Mahjong.Wait.Analysis

/-!
# Exhaustive four-tile wait computation

This module is intentionally outside the `Mahjong` library.  It enumerates all
legal four-tile multisets and computes the wait information that is useful for
studying one-mentsu standard-form tenpai shapes.
-/

namespace MahjongComputations.FourTile

open DecompositionCode
open DecompositionFinder

/-- A computed summary for one four-tile shape. -/
structure FourTileShapeReport where
  tiles : List Tile
  waits : List Tile
  kind : Option WaitKind
  candidateKinds : List WaitKind
  reducibility : Option WaitReducibility
  decompositionCodes : List Nat
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
    decompositionCodes := findAbstractDecompositionCode tiles }

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
          decompositionCodes := findAbstractDecompositionCode tiles }

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
