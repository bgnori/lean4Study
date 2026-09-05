import Mahjong.DirectWaitGeneration

namespace MahjongTests.DirectWaitGeneration

open _root_.DirectWaitGeneration
open _root_.WaitCompletionFinder

/-!
7枚形 (`n = 2`) について、全牌姿約1800万件や全 Seed 約1050万件ではなく、選択部品に
含まれる牌だけを待ち候補にした465,630件を生成する。そのうち物理制約と正規化条件を
満たす待ち導出は224,502件である。
-/
example :
    (seedCandidates 2).length = 465630 ∧
    (directSeeds 2).length = 224502 := by
  native_decide

private def testHand2345678 : List Tile := manzu [1, 2, 3, 4, 5, 6, 7]

/-- Finderの各結果は、同じ正規化牌姿とcompletionを持つ直接生成の待ち導出とちょうど対応する。 -/
example (found : WaitCompletion) :
    found ∈ findWaitCompletions testHand2345678 ↔
      ∃ n, ∃ derivation : WaitDerivation n,
        n ≤ standardHandMentsuCount ∧
        hand derivation = canonicalTiles testHand2345678 ∧
        completion derivation = found := by
  exact mem_findWaitCompletions_iff_exists_derivation _ _

end MahjongTests.DirectWaitGeneration
