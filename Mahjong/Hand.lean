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
abbrev tenTileHandSize : Nat := thirteenTileHandSize - mentsuTileCount

/-- 2面子を除去できる手牌サイズ。 -/
abbrev sevenTileHandSize : Nat := tenTileHandSize - mentsuTileCount

/-- 単騎だけの最小手牌サイズ。 -/
abbrev oneTileHandSize : Nat := fourTileHandSize - mentsuTileCount

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

`tanki` と `wait` は終端で、`mentsuThen` は完成面子を1つ取り除いたあと、
残りの手牌に対してさらに抽出を続ける。
-/
inductive HandExtraction
| tanki (tanki : Tanki) (taken : List PhysicalTile)
| wait (extraction : WaitExtraction) (taken : List PhysicalTile)
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

private noncomputable def waitTerminals (tiles : Finset PhysicalTile) : List HandExtraction :=
  WaitExtraction.all.filterMap fun extraction => do
    let taken ← takeExact tiles extraction.tiles
    some (.wait extraction taken)

/--
手牌から可能な抽出を列挙する。

`fuel` は再帰の深さで、完成面子を取り除きながら、最終的に単騎または4枚待ちへ到達する。
-/
noncomputable def fromTiles : Nat → Finset PhysicalTile → List HandExtraction
  | 0, tiles => tankiTerminals tiles ++ waitTerminals tiles
  | Nat.succ fuel, tiles =>
      tankiTerminals tiles ++
      waitTerminals tiles ++
      MentsuCandidate.all.flatMap fun mentsu =>
        match Chunk.takeTilesFrom tiles mentsu.tiles with
        | some (taken, rest) =>
            (fromTiles fuel rest).map fun remaining =>
              .mentsuThen mentsu taken remaining
        | none => []

/--
物理牌集合から `extraction` を正確に取り出せることを表す宣言的な仕様。

終端では牌を余さず使い切り、`mentsuThen` では完成面子を取った残りに対して
再帰的に仕様を満たすことを要求する。列挙関数 `fromTiles` には依存しないため、
分解不能な牌姿についてはこの型の証拠を構成できない。
-/
inductive Extracts : Nat → Finset PhysicalTile → HandExtraction → Prop
| tanki {fuel tiles tanki taken}
    (take : takeExact tiles tanki.tiles = some taken) :
    Extracts fuel tiles (.tanki tanki taken)
| wait {fuel tiles extraction taken}
    (take : takeExact tiles extraction.tiles = some taken) :
    Extracts fuel tiles (.wait extraction taken)
| mentsuThen {fuel tiles mentsu taken rest remaining}
    (take : Chunk.takeTilesFrom tiles mentsu.tiles = some (taken, rest))
    (next : Extracts fuel rest remaining) :
    Extracts (fuel + 1) tiles (.mentsuThen mentsu taken remaining)

private theorem mem_tankiTerminals_iff (tiles : Finset PhysicalTile)
    (result : HandExtraction) :
    result ∈ tankiTerminals tiles ↔
      ∃ tanki taken, takeExact tiles tanki.tiles = some taken ∧
        result = .tanki tanki taken := by
  simp only [tankiTerminals, List.mem_filterMap]
  constructor
  · rintro ⟨tanki, _, result⟩
    cases take : takeExact tiles tanki.tiles with
    | none => simp [take] at result
    | some taken =>
        simp [take] at result
        exact ⟨tanki, taken, take, result.symm⟩
  · rintro ⟨tanki, taken, take, rfl⟩
    exact ⟨tanki, by simp [Tanki.all], by simp [take]⟩

private theorem mem_waitTerminals_iff (tiles : Finset PhysicalTile)
    (result : HandExtraction) :
    result ∈ waitTerminals tiles ↔
      ∃ extraction taken, takeExact tiles extraction.tiles = some taken ∧
        result = .wait extraction taken := by
  simp only [waitTerminals, List.mem_filterMap]
  constructor
  · rintro ⟨extraction, _, result⟩
    cases take : takeExact tiles extraction.tiles with
    | none => simp [take] at result
    | some taken =>
        simp [take] at result
        exact ⟨extraction, taken, take, result.symm⟩
  · rintro ⟨extraction, taken, take, rfl⟩
    exact ⟨extraction, by simp [WaitExtraction.all], by simp [take]⟩

private theorem mem_mentsuExtractions_iff (fuel : Nat) (tiles : Finset PhysicalTile)
    (result : HandExtraction) :
    result ∈ MentsuCandidate.all.flatMap (fun mentsu =>
      match Chunk.takeTilesFrom tiles mentsu.tiles with
      | some (taken, rest) =>
          (fromTiles fuel rest).map fun remaining => .mentsuThen mentsu taken remaining
      | none => []) ↔
      ∃ mentsu taken rest remaining,
        Chunk.takeTilesFrom tiles mentsu.tiles = some (taken, rest) ∧
        remaining ∈ fromTiles fuel rest ∧
        result = .mentsuThen mentsu taken remaining := by
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨mentsu, _, member⟩
    cases take : Chunk.takeTilesFrom tiles mentsu.tiles with
    | none => simp [take] at member
    | some value =>
        obtain ⟨taken, rest⟩ := value
        simp only [take, List.mem_map] at member
        obtain ⟨remaining, next, rfl⟩ := member
        exact ⟨mentsu, taken, rest, remaining, take, next, rfl⟩
  · rintro ⟨mentsu, taken, rest, remaining, take, next, rfl⟩
    exact ⟨mentsu, by simp [MentsuCandidate.all], by simp [take, next]⟩

/-- `fromTiles` は宣言的な抽出仕様に対して健全かつ完全である。 -/
theorem mem_fromTiles_iff (fuel : Nat) (tiles : Finset PhysicalTile)
    (extraction : HandExtraction) :
    extraction ∈ fromTiles fuel tiles ↔ Extracts fuel tiles extraction := by
  induction fuel generalizing tiles extraction with
  | zero =>
      simp only [fromTiles, List.mem_append, mem_tankiTerminals_iff,
        mem_waitTerminals_iff]
      constructor
      · rintro (⟨tanki, taken, take, rfl⟩ | ⟨wait, taken, take, rfl⟩)
        · exact .tanki take
        · exact .wait take
      · intro extracted
        cases extracted with
        | tanki take => exact Or.inl ⟨_, _, take, rfl⟩
        | wait take => exact Or.inr ⟨_, _, take, rfl⟩
  | succ fuel ih =>
      simp only [fromTiles, List.mem_append, mem_tankiTerminals_iff,
        mem_waitTerminals_iff, mem_mentsuExtractions_iff]
      constructor
      · rintro ((⟨tanki, taken, take, rfl⟩ | ⟨wait, taken, take, rfl⟩) |
          ⟨mentsu, taken, rest, remaining, take, next, rfl⟩)
        · exact .tanki take
        · exact .wait take
        · exact .mentsuThen take ((ih rest remaining).mp next)
      · intro extracted
        cases extracted with
        | tanki take => exact Or.inl (Or.inl ⟨_, _, take, rfl⟩)
        | wait take => exact Or.inl (Or.inr ⟨_, _, take, rfl⟩)
        | mentsuThen take next =>
            exact Or.inr ⟨_, _, _, _, take, (ih _ _).mpr next, rfl⟩

end HandExtraction

namespace Hand

/-- 13枚手牌から単騎・4枚待ちまで降りるために取り除ける最大面子数。 -/
def maxMentsuRemovalCount : Nat := standardHandMentsuCount

/-- 手牌から得られる抽出候補を列挙する。 -/
noncomputable def extractions (hand : Hand) : List HandExtraction :=
  HandExtraction.fromTiles maxMentsuRemovalCount hand.toFinset

/-- 手牌の抽出列挙は、物理牌を正確に使い切る抽出仕様と同値である。 -/
theorem mem_extractions_iff (hand : Hand) (extraction : HandExtraction) :
    extraction ∈ hand.extractions ↔
      HandExtraction.Extracts maxMentsuRemovalCount hand.toFinset extraction := by
  exact HandExtraction.mem_fromTiles_iff _ _ _

end Hand
