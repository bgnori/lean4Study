import Mahjong.Hand

/-! # 待ち -/
/-! ## 待ち要素の定義 -/
/-! ### Hand one に対しては単騎のみ -/

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

def one_is_tenpai (tiles : Fin 1 ↪ { pt : PhysicalTile // pt ∈ deck }) :
    Tenpai (.one tiles) :=
  .tanki tiles (.tanki ((tiles 0).1).1) (by simp [Tanki.Matches, Tanki.tiles])

/-! ## 複合待ちの定義 -/
