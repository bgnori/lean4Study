import Mahjong.DirectWaitGeneration
import MahjongComputations.Common

/-!
# Exhaustive four-tile wait computation

This module is intentionally outside the `Mahjong` library.  It enumerates all
legal four-tile multisets and computes the wait information that is useful for
studying one-mentsu standard-form tenpai shapes.
-/

namespace MahjongComputations.FourTile

open DirectWaitGeneration
open WaitDecompositionCode
open WaitCompletionFinder

/-- A computed summary for one four-tile shape. -/
structure FourTileShapeReport where
  tiles : List Tile
  waits : List Tile
  reducibility : Option WaitReducibility
  waitDecompositionCodes : List Nat
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
    reducibility := determineReducibility tiles
    waitDecompositionCodes := findWaitDecompositionCodes tiles }

/-- Exhaustive four-tile tenpai reports. -/
def tenpaiReports : List FourTileShapeReport :=
  (allFourTileShapes.map report).filter fun report => !report.waits.isEmpty

private def directFourTileShapeReports (_ : Unit) : List WaitCompletionGroup :=
  groupWaitDerivations (directWaitDerivations 1)

private def directReport (report : WaitCompletionGroup) : FourTileShapeReport :=
  let completions := report.completions
  { tiles := report.tiles
    waits := waitsFromCompletions completions
    reducibility := determineReducibility report.tiles
    waitDecompositionCodes := waitDecompositionCodes completions }

/-- Number of normalized direct derivations enumerated for four-tile shapes. -/
def directDerivationCount : Nat :=
  (directWaitDerivations 1).length

/-- Four-tile tenpai reports computed by projecting direct derivations and grouping equal hands. -/
def directDerivationTenpaiReports : List FourTileShapeReport :=
  (directFourTileShapeReports ()).map directReport

/-- Irreducible four-tile tenpai shapes. -/
def irreducibleReports : List FourTileShapeReport :=
  tenpaiReports.filter fun report => report.reducibility == some .irreducible

example : allFourTileShapes.length = 66045 := by
  native_decide

end MahjongComputations.FourTile
