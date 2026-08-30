import Mahjong.FourTileWait
import Mahjong.Wait.Specification

/-!
# 4枚待ち分類の仕様

待ち分類の仕様本体は `Mahjong.Wait.Specification` に置く。
このモジュールは4枚ケースの名前をテストや互換性のために提供する。
-/

/-- 4枚ケースで使う基本形名。互換性とテスト名のために残す。 -/
abbrev FourTileProfile := WaitProfile

namespace FourTileSpecification

abbrev HasKuttsuki (profiles : List FourTileProfile) (taatsuProfile : FourTileProfile) : Prop :=
  WaitSpecification.HasKuttsuki profiles taatsuProfile

abbrev HasKuttsukiRyanmen (profiles : List FourTileProfile) : Prop :=
  WaitSpecification.HasKuttsukiRyanmen profiles

abbrev HasKuttsukiKanchan (profiles : List FourTileProfile) : Prop :=
  WaitSpecification.HasKuttsukiKanchan profiles

abbrev HasKuttsukiPenchan (profiles : List FourTileProfile) : Prop :=
  WaitSpecification.HasKuttsukiPenchan profiles

abbrev expectedKind (profiles : List FourTileProfile) : Option FourTileWaitKind :=
  WaitSpecification.expectedKind profiles

abbrev Classifies (profiles : List FourTileProfile) (kind : FourTileWaitKind) : Prop :=
  WaitSpecification.Classifies profiles kind

end FourTileSpecification
