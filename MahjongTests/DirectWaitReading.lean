import Mahjong.DirectWaitReading

namespace MahjongTests.DirectWaitReading

open _root_.DirectWaitReading
open _root_.WaitCompletionFinder

/-!
7枚形 (`n = 2`) について、全牌姿約1800万件や全 Seed 約1050万件ではなく、選択部品に
含まれる牌だけを待ち候補にした465,630件を生成する。そのうち物理制約と正規化条件を
満たす Reading の生成元は224,502件である。
-/
example :
    (seedCandidates 2).length = 465630 ∧
    (directSeeds 2).length = 224502 := by
  native_decide

private def testHand2345678 : List Tile := manzu [1, 2, 3, 4, 5, 6, 7]

/-- Finderの各結果は、同じ正規化牌姿とcompletionを持つ直接生成Readingとちょうど対応する。 -/
example (found : WaitCompletion) :
    found ∈ findWaitCompletions testHand2345678 ↔
      ∃ n, ∃ reading : Reading n,
        n ≤ standardHandMentsuCount ∧
        hand reading = canonicalTiles testHand2345678 ∧
        completion reading = found := by
  exact mem_findWaitCompletions_iff_exists_reading _ _

end MahjongTests.DirectWaitReading
