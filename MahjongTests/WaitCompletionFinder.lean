import Mahjong.WaitCompletionFinder

namespace MahjongTests.WaitCompletionFinder

open _root_.WaitCompletionFinder

private def testHandA : List Tile := Tile.numberedTiles .Manzu [2, 3, 4, 4, 4] ++
  Tile.numberedTiles .Souzu [7, 7]
private def testHandB : List Tile := Tile.numberedTiles .Manzu [1, 1, 2, 2, 3, 3, 4, 4, 5, 5]
private def testHandC : List Tile := Tile.numberedTiles .Souzu [2, 2, 3, 3, 4, 4, 5, 5, 6, 6]
private def testHandD : List Tile := Tile.numberedTiles .Manzu [1, 1, 2, 2, 3, 3, 4, 4] ++
  Tile.numberedTiles .Souzu [6, 6]
private def testHand3456678 : List Tile := manzu [2, 3, 4, 5, 5, 6, 7]
private def testHand2345678 : List Tile := manzu [1, 2, 3, 4, 5, 6, 7]
private def testHand3334556 : List Tile := manzu [2, 2, 2, 3, 4, 4, 5]
private def testHand3335678 : List Tile := manzu [2, 2, 2, 4, 5, 6, 7]
private def testHand3335567 : List Tile := manzu [2, 2, 2, 4, 4, 5, 6]
private def testHand3335777 : List Tile := manzu [2, 2, 2, 4, 6, 6, 6]
private def testHand2345555678 : List Tile := manzu [1, 2, 3, 4, 4, 4, 4, 5, 6, 7]

private def manzuPair (rank : Rank) : TileChunk :=
  .pair (.numbered .Manzu rank)

private def manzuShuntsu (start : Nat) (valid : start < shuntsuStartCount := by decide) : TileChunk :=
  .shuntsu .Manzu ⟨start, valid⟩

private def manzuKoutsu (rank : Rank) : TileChunk :=
  .koutsu (.numbered .Manzu rank)

private def manzuWaitCompletion (wait : Rank) (winningChunks : List TileChunk) : WaitCompletion :=
  { wait := .numbered .Manzu wait, winningChunks }

example :
    waitingTiles testHandA = manzu [1, 4] ++ souzu [7] ∧
    waitingTiles testHandB = manzu [1, 2, 4, 5] ∧
    waitingTiles testHandC = souzu [2, 3, 5, 6] ∧
    waitingTiles testHandD = manzu [1, 4] ++ souzu [6] ∧
    waitingTiles testHand2345555678 = manzu [1, 7] ∧
    waitingTiles (manzu [0, 1]) = [] ∧
    waitingTiles (manzu [0, 0, 0, 0, 0, 1, 2]) = [] ∧
    findWaitCompletions testHand3456678 =
      [manzuWaitCompletion 2 [manzuPair 2, manzuShuntsu 3, manzuShuntsu 5],
       manzuWaitCompletion 5 [manzuPair 5, manzuShuntsu 2, manzuShuntsu 5],
       manzuWaitCompletion 8 [manzuPair 5, manzuShuntsu 2, manzuShuntsu 6]] ∧
    (findWaitCompletions testHand3456678).length = 3 ∧
    findWaitCompletions testHand2345678 =
      [manzuWaitCompletion 1 [manzuPair 1, manzuShuntsu 2, manzuShuntsu 5],
       manzuWaitCompletion 4 [manzuPair 4, manzuShuntsu 1, manzuShuntsu 5],
       manzuWaitCompletion 7 [manzuPair 7, manzuShuntsu 1, manzuShuntsu 4]] ∧
    (findWaitCompletions testHand2345678).length = 3 ∧
    findWaitCompletions testHand3334556 =
      [manzuWaitCompletion 3 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 3],
       manzuWaitCompletion 4 [manzuPair 4, manzuShuntsu 3, manzuKoutsu 2],
       manzuWaitCompletion 6 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 4]] ∧
    (findWaitCompletions testHand3334556).length = 3 ∧
    findWaitCompletions testHand3335678 =
      [manzuWaitCompletion 3 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 5],
       manzuWaitCompletion 4 [manzuPair 4, manzuShuntsu 5, manzuKoutsu 2],
       manzuWaitCompletion 7 [manzuPair 7, manzuShuntsu 4, manzuKoutsu 2]] ∧
    (findWaitCompletions testHand3335678).length = 3 ∧
    findWaitCompletions testHand3335567 =
      [manzuWaitCompletion 3 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 4],
       manzuWaitCompletion 4 [manzuPair 4, manzuShuntsu 4, manzuKoutsu 2],
      manzuWaitCompletion 7 [manzuPair 4, manzuShuntsu 5, manzuKoutsu 2]] ∧
    (findWaitCompletions testHand3335567).length = 3 ∧
    findWaitCompletions testHand3335777 =
      [manzuWaitCompletion 3 [manzuPair 2, manzuShuntsu 2, manzuKoutsu 6],
       manzuWaitCompletion 4 [manzuPair 4, manzuKoutsu 2, manzuKoutsu 6],
       manzuWaitCompletion 5 [manzuPair 6, manzuShuntsu 4, manzuKoutsu 2]] ∧
    (findWaitCompletions testHand3335777).length = 3 ∧
    findWaitCompletions testHand2345555678 =
      [manzuWaitCompletion 1
          [manzuPair 1, manzuShuntsu 2, manzuShuntsu 5, manzuKoutsu 4],
        manzuWaitCompletion 7
          [manzuPair 7, manzuShuntsu 1, manzuShuntsu 4, manzuKoutsu 4]] ∧
    (findWaitCompletions testHand2345555678).length = 2 := by
  native_decide

end MahjongTests.WaitCompletionFinder
