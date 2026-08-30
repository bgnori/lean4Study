import Mahjong.FourTileWait

/-!
# 手牌と抽出列挙

このモジュールでは、物理牌の集合としての手牌と、そこから待ち分類に必要な部品を
取り出す列挙処理を定義する。

通常形では、聴牌時の手牌枚数は `3n + 1` になる。ここでは学習対象として
1枚、4枚、7枚、10枚、13枚の手牌だけを扱う。
-/
/-- 通常形聴牌として扱う最大手牌サイズ。 -/
abbrev thirteenTileHandSize : Nat := standardTenpaiHandSize standardHandMentsuCount

/-- 3面子を除去できる手牌サイズ。 -/
abbrev tenTileHandSize : Nat := standardTenpaiHandSize 3

/-- 2面子を除去できる手牌サイズ。 -/
abbrev sevenTileHandSize : Nat := standardTenpaiHandSize 2

/-- 単騎だけの最小手牌サイズ。 -/
abbrev oneTileHandSize : Nat := standardTenpaiHandSize 0

/-- 解析対象にする手牌サイズ。各手牌は `deck` から重複なく取られた物理牌で表す。 -/
inductive Hand where
  | thirteen (tiles : Fin thirteenTileHandSize ↪ { pt : PhysicalTile // pt ∈ deck })
  | ten (tiles : Fin tenTileHandSize ↪ { pt : PhysicalTile // pt ∈ deck })
  | seven (tiles : Fin sevenTileHandSize ↪ { pt : PhysicalTile // pt ∈ deck })
  | four (tiles : Fin fourTileHandSize ↪ { pt : PhysicalTile // pt ∈ deck })
  | one (tiles : Fin oneTileHandSize ↪ { pt : PhysicalTile // pt ∈ deck })

namespace Hand

/-- 手牌を物理牌の有限集合に変換する。 -/
noncomputable def toFinset : Hand → Finset PhysicalTile
  | .thirteen tiles => (Finset.univ : Finset (Fin thirteenTileHandSize)).image fun i => (tiles i).1
  | .ten tiles => (Finset.univ : Finset (Fin tenTileHandSize)).image fun i => (tiles i).1
  | .seven tiles => (Finset.univ : Finset (Fin sevenTileHandSize)).image fun i => (tiles i).1
  | .four tiles => (Finset.univ : Finset (Fin fourTileHandSize)).image fun i => (tiles i).1
  | .one tiles => (Finset.univ : Finset (Fin oneTileHandSize)).image fun i => (tiles i).1

/-- 手牌を通常形の意味論が扱う牌種列へ変換する。 -/
noncomputable def tileTypes (hand : Hand) : List Tile :=
  hand.toFinset.toList.map Prod.fst

end Hand

/-!
## 手牌からの取り方の列挙
-/
/--
手牌から取り出せる待ち分類の構造。

`tanki` と `four` は終端で、`mentsuThen` は完成面子を1つ取り除いたあと、
残りの手牌に対してさらに抽出を続ける。
-/
inductive HandExtraction
| tanki (tanki : Tanki) (taken : List PhysicalTile)
| four (extraction : FourTileExtraction) (taken : List PhysicalTile)
| mentsuThen (mentsu : MentsuCandidate) (taken : List PhysicalTile)
    (remaining : HandExtraction)
deriving Repr

namespace HandExtraction

/-- 指定された牌種列をちょうど取り出せる場合だけ、取り出した物理牌を返す。 -/
private noncomputable def takeExact (tiles : Finset PhysicalTile) (wanted : List Tile) :
    Option (List PhysicalTile) := do
  let (taken, rest) ← Chunk.takeTilesFrom tiles wanted
  if rest = ∅ then
    some taken
  else
    none

private noncomputable def tankiTerminals (tiles : Finset PhysicalTile) : List HandExtraction :=
  Tanki.all.filterMap fun tanki => do
    let taken ← takeExact tiles tanki.tiles
    some (.tanki tanki taken)

private noncomputable def fourTerminals (tiles : Finset PhysicalTile) : List HandExtraction :=
  FourTileExtraction.all.filterMap fun extraction => do
    let taken ← takeExact tiles extraction.tiles
    some (.four extraction taken)

/--
手牌から可能な抽出を列挙する。

`fuel` は再帰の深さで、完成面子を取り除きながら、最終的に単騎または4枚待ちへ到達する。
-/
noncomputable def fromTiles : Nat → Finset PhysicalTile → List HandExtraction
  | 0, tiles => tankiTerminals tiles ++ fourTerminals tiles
  | Nat.succ fuel, tiles =>
      tankiTerminals tiles ++
      fourTerminals tiles ++
      List.flatten (MentsuCandidate.all.map fun mentsu =>
        match Chunk.takeTilesFrom tiles mentsu.tiles with
        | some (taken, rest) =>
            (fromTiles fuel rest).map fun remaining =>
              .mentsuThen mentsu taken remaining
        | none => [])

end HandExtraction

namespace Hand

/-- 13枚手牌から単騎・4枚待ちまで降りるために取り除ける最大面子数。 -/
def maxMentsuRemovalCount : Nat := standardHandMentsuCount

/-- 手牌から得られる抽出候補を列挙する。 -/
noncomputable def extractions (hand : Hand) : List HandExtraction :=
  HandExtraction.fromTiles maxMentsuRemovalCount hand.toFinset

end Hand
