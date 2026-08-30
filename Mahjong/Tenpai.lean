import Mahjong.Hand
import Mahjong.DecompositionFinder

/-!
# 聴牌の証拠

`Tenpai hand` は、手牌を牌種列へ写した上で `DecompositionFinder.Wait` に結び付ける。
待ちの意味論は手牌枚数によらず共通であり、4枚・7枚専用の証拠型は使わない。
-/

/-- 物理的な手牌に結び付いた、通常形の待ちの証拠。 -/
abbrev Tenpai (hand : Hand) := DecompositionFinder.Wait hand.tileTypes
