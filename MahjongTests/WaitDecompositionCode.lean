import Mahjong.WaitDecompositionCode

namespace MahjongTests.WaitDecompositionCode

open _root_.WaitDecompositionCode
open _root_.WaitCompletionFinder

private def testHand2345678 : List Tile := manzu [1, 2, 3, 4, 5, 6, 7]
private def testHand1234 : List Tile := manzu [0, 1, 2, 3]
private def testHand1167888 : List Tile := manzu [0, 0, 5, 6, 7, 7, 7]
private def testHand1166678 : List Tile := manzu [0, 0, 5, 5, 5, 6, 7]

private def isIrreducibleTenpai (tiles : List Tile) : Bool :=
  !(canReduceMentsuPreservingWaitCores tiles)

example :
  waitCoreExtractions (findWaitCompletions testHand1234) =
      [{ wait := .numbered .Manzu 0,
         core := [{ kind := .tanki, tiles := [.numbered .Manzu 0] }],
         removedMentsu := [{ kind := .shuntsu, tiles := manzu [1, 2, 3] }] },
       { wait := .numbered .Manzu 3,
         core := [{ kind := .tanki, tiles := [.numbered .Manzu 3] }],
         removedMentsu := [{ kind := .shuntsu, tiles := manzu [0, 1, 2] }] }] := by
  native_decide

example :
    findWaitCores (manzu [0, 0, 0, 3]) = findWaitCores (manzu [3]) ∧
    canReduceMentsuPreservingWaitCores (manzu [0, 0, 0, 3]) = true ∧
    findWaitCores testHand1234 != findWaitCores (manzu [0]) ∧
    findWaitCores testHand1234 != findWaitCores (manzu [3]) ∧
    canReduceMentsuPreservingWaitCores testHand1234 = false := by
  native_decide

example :
  waitKindDecompositions (findWaitCompletions testHand2345678) =
      [{ wait := .numbered .Manzu 1, components := [.tanki, .shuntsu, .shuntsu] },
       { wait := .numbered .Manzu 4, components := [.tanki, .shuntsu, .shuntsu] },
       { wait := .numbered .Manzu 7, components := [.tanki, .shuntsu, .shuntsu] }] ∧
    waitDecompositionCodeEntries (findWaitCompletions testHand2345678) =
      [{ wait := .numbered .Manzu 1, code := 338 },
       { wait := .numbered .Manzu 4, code := 338 },
       { wait := .numbered .Manzu 7, code := 338 }] ∧
    findWaitDecompositionCodes testHand2345678 = [338] ∧
    findWaitDecompositionCodes testHand1167888 = [117, 255] ∧
    findWaitDecompositionCodes testHand1166678 = [117, 255] ∧
    findWaitDecompositionCodes testHand1167888 =
      findWaitDecompositionCodes testHand1166678 ∧
    irreducibleSingleSuitSevenTileExamples.length = 53 ∧
    irreducibleSingleSuitSevenTileExamples.all
      (fun entry => isIrreducibleTenpai entry.2) = true ∧
    irreducibleSevenTileWaitDecompositionCodeClasses.length = 26 ∧
    irreducibleSevenTileWaitDecompositionCodeClasses.find? (fun entry =>
      entry.1 == [117, 255]) = some
        ([117, 255],
         ["1178999m", "1167888m", "1166678m", "1156777m", "1155567m",
          "1145666m", "1144456m", "1134555m", "1133345m", "1122234m",
          "1112399m", "1112388m", "1112377m", "1112366m", "1112355m"]) := by
  native_decide

end MahjongTests.WaitDecompositionCode
