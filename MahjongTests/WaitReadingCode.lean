import Mahjong.WaitReadingCode
import Mahjong.Wait.Analysis

namespace MahjongTests.WaitReadingCode

open _root_.WaitReadingCode
open _root_.WaitCompletionFinder

private def testHand2345678 : List Tile := manzu [1, 2, 3, 4, 5, 6, 7]
private def testHand1234 : List Tile := manzu [0, 1, 2, 3]
private def testHand1167888 : List Tile := manzu [0, 0, 5, 6, 7, 7, 7]
private def testHand1166678 : List Tile := manzu [0, 0, 5, 5, 5, 6, 7]

private def isIrreducibleTenpai (tiles : List Tile) : Bool :=
  !(canReduceMentsuPreservingWaitCores tiles)

example :
    findIrreducibleWaitReadings testHand1234 =
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
    canReduceMentsuPreservingWaitCores testHand1234 = false ∧
    WaitAnalysis.classifyWait testHand1234 = some .nobetan ∧
    WaitAnalysis.classifyWait (manzu [3]) = some .tanki := by
  native_decide

example :
    findAbstractWaitReadings testHand2345678 =
      [{ wait := .numbered .Manzu 1, components := [.tanki, .shuntsu, .shuntsu] },
       { wait := .numbered .Manzu 4, components := [.tanki, .shuntsu, .shuntsu] },
       { wait := .numbered .Manzu 7, components := [.tanki, .shuntsu, .shuntsu] }] ∧
    findWaitReadingCodeEntries testHand2345678 =
      [{ wait := .numbered .Manzu 1, code := 338 },
       { wait := .numbered .Manzu 4, code := 338 },
       { wait := .numbered .Manzu 7, code := 338 }] ∧
    findAbstractWaitReadingCodeWithWait testHand2345678 =
      [(338, .numbered .Manzu 1),
       (338, .numbered .Manzu 4),
       (338, .numbered .Manzu 7)] ∧
    findAbstractWaitReadingCode testHand2345678 = [338] ∧
    findAbstractWaitReadingCode testHand1167888 = [117, 255] ∧
    findAbstractWaitReadingCode testHand1166678 = [117, 255] ∧
    findAbstractWaitReadingCode testHand1167888 =
      findAbstractWaitReadingCode testHand1166678 ∧
    irreducibleSingleSuitSevenTileExamples.length = 53 ∧
    irreducibleSingleSuitSevenTileExamples.all
      (fun entry => isIrreducibleTenpai entry.2) = true ∧
    irreducibleSevenTileAbstractWaitReadingClasses.length = 26 ∧
    irreducibleSevenTileAbstractWaitReadingClasses.find? (fun entry =>
      entry.1 == [117, 255]) = some
        ([117, 255],
         ["1178999m", "1167888m", "1166678m", "1156777m", "1155567m",
          "1145666m", "1144456m", "1134555m", "1133345m", "1122234m",
          "1112399m", "1112388m", "1112377m", "1112366m", "1112355m"]) := by
  native_decide

end MahjongTests.WaitReadingCode
