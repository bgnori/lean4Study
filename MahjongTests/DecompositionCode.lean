import Mahjong.DecompositionCode

namespace MahjongTests.DecompositionCode

open _root_.DecompositionCode
open _root_.DecompositionFinder

private def testHand2345678 : List Tile := manzu [1, 2, 3, 4, 5, 6, 7]
private def testHand1167888 : List Tile := manzu [0, 0, 5, 6, 7, 7, 7]
private def testHand1166678 : List Tile := manzu [0, 0, 5, 5, 5, 6, 7]

private def isIrreducibleTenpai (tiles : List Tile) : Bool :=
  if tenpai : IsTenpai tiles then
    decide (IsIrreducible tiles tenpai)
  else
    false

example :
    findAbstractDecompositionExtractions testHand2345678 =
      [{ wait := .numbered .Manzu 1, components := [.tanki, .shuntsu, .shuntsu] },
       { wait := .numbered .Manzu 4, components := [.tanki, .shuntsu, .shuntsu] },
       { wait := .numbered .Manzu 7, components := [.tanki, .shuntsu, .shuntsu] }] ∧
    findDecompositionCodeEntries testHand2345678 =
      [{ wait := .numbered .Manzu 1, code := 338 },
       { wait := .numbered .Manzu 4, code := 338 },
       { wait := .numbered .Manzu 7, code := 338 }] ∧
    findAbstractDecompositionCodeWithWait testHand2345678 =
      [(338, .numbered .Manzu 1),
       (338, .numbered .Manzu 4),
       (338, .numbered .Manzu 7)] ∧
    findAbstractDecompositionCode testHand2345678 = [338] ∧
    findAbstractDecompositionCode testHand1167888 = [117, 255] ∧
    findAbstractDecompositionCode testHand1166678 = [117, 255] ∧
    findAbstractDecompositionCode testHand1167888 =
      findAbstractDecompositionCode testHand1166678 ∧
    irreducibleSingleSuitSevenTileExamples.length = 53 ∧
    irreducibleSingleSuitSevenTileExamples.all
      (fun entry => isIrreducibleTenpai entry.2) = true ∧
    irreducibleSevenTileAbstractDecompositionClasses.length = 26 ∧
    irreducibleSevenTileAbstractDecompositionClasses.find? (fun entry =>
      entry.1 == [117, 255]) = some
        ([117, 255],
         ["1178999m", "1167888m", "1166678m", "1156777m", "1155567m",
          "1145666m", "1144456m", "1134555m", "1133345m", "1122234m",
          "1112399m", "1112388m", "1112377m", "1112366m", "1112355m"]) := by
  native_decide

end MahjongTests.DecompositionCode
