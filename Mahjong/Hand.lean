import Mahjong.SevenTileWait

/-!
# 手牌
1, 4, 7, 10, 13だけを考えるのでOK.
-/
inductive Hand where
  | thirteen (tiles : Fin 13 ↪ { pt : PhysicalTile // pt ∈ deck })
  | ten (tiles : Fin 10 ↪ { pt : PhysicalTile // pt ∈ deck })
  | seven (tiles : Fin 7 ↪ { pt : PhysicalTile // pt ∈ deck })
  | four (tiles : Fin 4 ↪ { pt : PhysicalTile // pt ∈ deck })
  | one (tiles : Fin 1 ↪ { pt : PhysicalTile // pt ∈ deck })

namespace Hand

noncomputable def toFinset : Hand → Finset PhysicalTile
  | .thirteen tiles => (Finset.univ : Finset (Fin 13)).image fun i => (tiles i).1
  | .ten tiles => (Finset.univ : Finset (Fin 10)).image fun i => (tiles i).1
  | .seven tiles => (Finset.univ : Finset (Fin 7)).image fun i => (tiles i).1
  | .four tiles => (Finset.univ : Finset (Fin 4)).image fun i => (tiles i).1
  | .one tiles => (Finset.univ : Finset (Fin 1)).image fun i => (tiles i).1

end Hand

/-!
## 手牌からの取り方の列挙
-/
inductive HandExtraction
| tanki (tanki : Tanki) (taken : List PhysicalTile)
| four (extraction : FourTileExtraction) (taken : List PhysicalTile)
| mentsuThen (mentsu : MentsuCandidate) (taken : List PhysicalTile)
    (remaining : HandExtraction)
deriving Repr

namespace HandExtraction

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

noncomputable def extractions (hand : Hand) : List HandExtraction :=
  HandExtraction.fromTiles 4 hand.toFinset

end Hand
