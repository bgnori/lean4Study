import Mahjong.DirectWaitReading

namespace MahjongTests.DirectWaitReading

open _root_.DirectWaitReading

/-!
7枚形 (`n = 2`) について、全牌姿約1800万件や全 Seed 約1050万件ではなく、選択部品に
含まれる牌だけを待ち候補にした465,630件を生成する。そのうち物理制約と正規化条件を
満たす Reading の生成元は224,502件である。
-/
example :
    (seedCandidates 2).length = 465630 ∧
    (directSeeds 2).length = 224502 := by
  native_decide

end MahjongTests.DirectWaitReading
