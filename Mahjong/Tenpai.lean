import Mahjong.Hand

/-!
# 聴牌の証拠

`Tenpai hand` は、手牌 `hand` がどの待ち証拠を持つかを表す依存型である。
現在は学習用に、1枚、4枚、7枚の聴牌証拠を扱う。
-/

/-- 手牌サイズごとの聴牌証拠。 -/
inductive Tenpai : Hand → Type
  | tanki
      (tiles : Fin 1 ↪ { pt : PhysicalTile // pt ∈ deck })
      (wait : Tanki)
      (lastTileMatches : wait.Matches (tiles 0).1) :
      Tenpai (.one tiles)
  | four
      (tiles : Fin 4 ↪ { pt : PhysicalTile // pt ∈ deck })
      (wait : FourTileWait) :
      Tenpai (.four tiles)
    | seven
      (tiles : Fin 7 ↪ { pt : PhysicalTile // pt ∈ deck })
      (wait : SevenTileWait) :
      Tenpai (.seven tiles)

/-- 1枚手牌は、その1枚を単騎として待つ聴牌である。 -/
def one_is_tenpai (tiles : Fin 1 ↪ { pt : PhysicalTile // pt ∈ deck }) :
    Tenpai (.one tiles) :=
  .tanki tiles (.tanki ((tiles 0).1).1) (by simp [Tanki.Matches, Tanki.tiles])

/-! ## 複合待ちの定義 -/
