import Mahjong.WaitReadingCode
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Encodable.Pi
import Mathlib.Logic.Equiv.List

/-!
# テンパイ形の直接生成

7枚の牌姿を先に全列挙すると、非テンパイ形を含む約1800万件を探索することになる。
このモジュールでは逆に、`2 + 3n` 枚の通常和了形（雀頭1個と `n` 個の面子）を作り、
その部品のどれかから待ち牌を1枚取り除いて `1 + 3n` 枚のテンパイ形を得る。

生成の選択は次の3段階に対応する。

1. 雀頭と `n` 個の完成面子を選ぶ。
2. 待ち牌を取り除く部品を選ぶ。
3. その部品内の牌を待ち牌として選ぶ。

3によって、単騎、対子、両面、辺張、嵌張のいずれかが生じ、選ばれなかった部品は
順子または刻子として残る。`Reading n` は、この生成元のうち物理的に合法で
正規化済みのものだけを集めた有限型である。

`readingEquiv` は `Fin (Fintype.card (Reading n))` と全 Reading の全単射が存在することを
示す非計算的な仕様であり、実行には使わない。実行用の `directReadings` は面子列を再帰生成し、
選択部品に実際に含まれる牌だけを待ち牌候補にする。`directSeeds_sound` と
`directSeeds_complete` は、この削減が妥当な Reading を増やしも取りこぼしもしないことを示す。

同じ牌姿へ射影される異なる Reading は、異なる待ち牌や和了分割に由来する曖昧さである。
`readingsForHand` をこの射影のファイバーとして定義し、
`directly_generated_readings_complete` により、直接生成器がその曖昧さを過不足なく回収する
ことを示す。
-/

namespace DirectWaitReading

open WaitCompletionFinder
open WaitReadingCode

variable {n : Nat}

/-- 完成形のどの部品から待ち牌を取り除くか。 -/
inductive ComponentIndex (n : Nat)
| pair
| mentsu (index : Fin n)
deriving BEq, DecidableEq, Fintype, Repr

/-- 雀頭1個と `n` 個の面子からなる `2 + 3n` 枚の通常和了形。 -/
structure WinningShape (n : Nat) where
  pair : Toitsu
  mentsu : Fin n → MentsuCandidate
deriving BEq, DecidableEq, Fintype

namespace WinningShape

/-- 完成形の指定された部品を取り出す。 -/
def chunk (shape : WinningShape n) : ComponentIndex n → TileChunk
  | .pair => .inl shape.pair
  | .mentsu index => .inr (shape.mentsu index)

/-- 雀頭を先頭に置いた完成部品列。 -/
def chunks (shape : WinningShape n) : List TileChunk :=
  .inl shape.pair :: (List.ofFn shape.mentsu).map fun mentsu => (.inr mentsu : TileChunk)

/-- 完成形を構成する全牌。 -/
def tiles (shape : WinningShape n) : List Tile :=
  shape.chunks.flatMap TileChunk.tiles

end WinningShape

/-- 正規化前の直接生成パラメータ。 -/
structure Seed (n : Nat) where
  shape : WinningShape n
  selected : ComponentIndex n
  wait : Tile
deriving BEq, DecidableEq, Fintype

private def chunkOrderKey : TileChunk → Nat
  | .inl (.toitsu tile) => tile.orderKey
  | .inr (.shuntsu (.shuntsu suit start)) =>
      Tile.count + suit.orderKey * shuntsuStartCount + start.val
  | .inr (.koutsu tile) =>
      Tile.count + Suit.count * shuntsuStartCount + tile.orderKey

private def componentKindWithoutWait (wait : Tile) : TileChunk → Option WaitReadingComponentKind
  | .inl (.toitsu tile) =>
      if tile == wait then some .tanki else none
  | .inr (.koutsu tile) =>
      if tile == wait then some .toitsu else none
  | .inr (.shuntsu (.shuntsu suit start)) =>
      match wait with
      | .honor _ => none
      | .numbered waitSuit rank =>
          if waitSuit != suit then none
          else if rank == start.firstRank then
            some (if start.isLast then .penchan else .ryanmen)
          else if rank == start.middleRank then some .kanchan
          else if rank == start.lastRank then
            some (if start.isFirst then .penchan else .ryanmen)
          else none

private def keysNondecreasing : List Nat → Bool
  | [] | [_] => true
  | first :: second :: rest => first ≤ second && keysNondecreasing (second :: rest)

private def mentsuCanonical (shape : WinningShape n) : Bool :=
  keysNondecreasing ((List.ofFn shape.mentsu).map fun mentsu =>
    chunkOrderKey (.inr mentsu))

private def selectedIsCanonical (seed : Seed n) : Bool :=
  match seed.selected with
  | .pair => true
  | .mentsu selected =>
      ((List.ofFn seed.shape.mentsu).take selected.val).all fun earlier =>
        earlier != seed.shape.mentsu selected

private def hasLegalTileCounts (tiles : List Tile) : Bool :=
  Tile.all.all fun tile => tiles.count tile ≤ copiesPerTile

/--
直接生成パラメータの妥当性。

待ち牌が選択部品を実際に不完全形へ変え、完成形が4枚制限を守ることに加え、面子順と
同一面子の選択を正規化する。後者は、面子の並べ替えや同一面子の別の出現位置だけが違う
生成元を、別 Reading と誤って数えないために必要である。
-/
def Seed.valid (seed : Seed n) : Bool :=
  (componentKindWithoutWait seed.wait (seed.shape.chunk seed.selected)).isSome &&
  hasLegalTileCounts seed.shape.tiles &&
  mentsuCanonical seed.shape &&
  selectedIsCanonical seed

/-- `n` 面子の完成形から直接生成できる、正規化済みの全 Reading。 -/
abbrev Reading (n : Nat) := { seed : Seed n // seed.valid }

private theorem wait_mem_chunk_of_componentKind_isSome
    (wait : Tile) (chunk : TileChunk)
    (valid : (componentKindWithoutWait wait chunk).isSome = true) :
    wait ∈ chunk.tiles := by
  rcases chunk with pair | mentsu
  · rcases pair with ⟨tile⟩
    simp only [componentKindWithoutWait] at valid
    split at valid
    · have tileEq : tile = wait := by simpa using ‹(tile == wait) = true›
      subst tile
      simp [TileChunk.tiles, Toitsu.tiles]
    · simp at valid
  · rcases mentsu with sequence | tile
    · rcases sequence with ⟨suit, start⟩
      cases wait with
      | honor honor => simp [componentKindWithoutWait] at valid
      | numbered waitSuit rank =>
          by_cases sameSuit : waitSuit = suit
          · subst waitSuit
            by_cases first : rank = start.firstRank
            · subst rank
              simp [TileChunk.tiles, MentsuCandidate.tiles, Shuntsu.tiles]
            · by_cases middle : rank = start.middleRank
              · subst rank
                simp [TileChunk.tiles, MentsuCandidate.tiles, Shuntsu.tiles]
              · by_cases last : rank = start.lastRank
                · subst rank
                  simp [TileChunk.tiles, MentsuCandidate.tiles, Shuntsu.tiles]
                · simp [componentKindWithoutWait, first, middle, last] at valid
          · simp [componentKindWithoutWait, sameSuit] at valid
    · simp only [componentKindWithoutWait] at valid
      split at valid
      · have tileEq : tile = wait := by simpa using ‹(tile == wait) = true›
        subst tile
        simp [TileChunk.tiles, MentsuCandidate.tiles]
      · simp at valid

/-!
## 直接生成器

`Fintype` から `Seed n` 全体を列挙すると、待ち牌について常に34種類を試すことになる。
さらに、有限関数全体を一度に `Finset` 化すると大きな中間データ構造が必要になる。
以下では面子関数をリストとして再帰生成し、完成形と選択部品を選んだ後、待ち牌候補を
その部品に実際に含まれる最大3種類へ限定する。
-/

/-- 順子21種と刻子34種からなる、実行可能な完成面子候補リスト。 -/
def mentsuCandidates : List MentsuCandidate :=
  (Suit.all.flatMap fun suit =>
    List.ofFn fun start : ShuntsuStart => MentsuCandidate.shuntsu (.shuntsu suit start)) ++
  Tile.all.map MentsuCandidate.koutsu

private theorem mem_mentsuCandidates (mentsu : MentsuCandidate) :
    mentsu ∈ mentsuCandidates := by
  cases mentsu with
  | shuntsu sequence =>
      rcases sequence with ⟨suit, start⟩
      simp only [mentsuCandidates, List.mem_append, List.mem_flatMap]
      left
      refine ⟨suit, by cases suit <;> simp [Suit.all], ?_⟩
      exact List.mem_ofFn.mpr ⟨start, rfl⟩
  | koutsu tile =>
      simp [mentsuCandidates, Tile.mem_all tile]

/-- `n` 個の完成面子の全列。全関数の `Finset` を構築せず、先頭追加で生成する。 -/
def mentsuFunctions : (n : Nat) → List (Fin n → MentsuCandidate)
  | 0 => [fun index => Fin.elim0 index]
  | n + 1 =>
      mentsuCandidates.flatMap fun first =>
        (mentsuFunctions n).map fun rest index => Fin.cases first rest index

/-- 任意の面子関数は再帰生成リストに含まれる。 -/
private theorem mem_mentsuFunctions (mentsu : Fin n → MentsuCandidate) :
    mentsu ∈ mentsuFunctions n := by
  induction n with
  | zero =>
      have emptyFunction : mentsu = fun index => Fin.elim0 index := by
        funext index
        exact Fin.elim0 index
      simp [mentsuFunctions, emptyFunction]
  | succ n inductionHypothesis =>
      let rest : Fin n → MentsuCandidate := fun index => mentsu index.succ
      have restMember := inductionHypothesis rest
      simp only [mentsuFunctions, List.mem_flatMap]
      refine ⟨mentsu 0, mem_mentsuCandidates (mentsu 0), ?_⟩
      apply List.mem_map.mpr
      refine ⟨rest, restMember, ?_⟩
      funext index
      exact Fin.cases rfl (fun _ => rfl) index

/-- 雀頭と再帰生成した面子列から作る全完成形。 -/
def winningShapes (n : Nat) : List (WinningShape n) :=
  Tile.all.flatMap fun tile =>
    (mentsuFunctions n).map fun mentsu => { pair := .toitsu tile, mentsu }

private theorem mem_winningShapes (shape : WinningShape n) :
    shape ∈ winningShapes n := by
  rcases shape with ⟨⟨tile⟩, mentsu⟩
  simp [winningShapes, Tile.mem_all tile, mem_mentsuFunctions mentsu]

/-- 雀頭または `n` 個の面子から選ぶ全部品位置。 -/
def componentIndices (n : Nat) : List (ComponentIndex n) :=
  .pair :: List.ofFn ComponentIndex.mentsu

private theorem mem_componentIndices (selected : ComponentIndex n) :
    selected ∈ componentIndices n := by
  cases selected with
  | pair => simp [componentIndices]
  | mentsu index =>
      simp only [componentIndices, List.mem_cons]
      right
      exact List.mem_ofFn.mpr ⟨index, rfl⟩

/-- 完成形と選択部品から、そこに含まれる牌だけを待ち牌候補として作る。 -/
def seedCandidates (n : Nat) : List (Seed n) :=
  (winningShapes n).flatMap fun shape =>
    (componentIndices n).flatMap fun selected =>
      (shape.chunk selected).tiles.dedup.map fun wait =>
        { shape, selected, wait }

/-- 直接生成した候補から、物理制約と正規化条件を満たすものだけを残す。 -/
def directSeeds (n : Nat) : List (Seed n) :=
  (seedCandidates n).filter fun seed => seed.valid

/-- 直接生成器は妥当でない Seed を出力しない。 -/
theorem directSeeds_sound {seed : Seed n} (member : seed ∈ directSeeds n) :
    seed.valid := by
  exact (List.mem_filter.mp member).2

/-- 妥当な Seed は必ず直接生成器の出力に含まれる。 -/
theorem directSeeds_complete {seed : Seed n} (valid : seed.valid) :
    seed ∈ directSeeds n := by
  have validParts :
      (((componentKindWithoutWait seed.wait
          (seed.shape.chunk seed.selected)).isSome = true ∧
        hasLegalTileCounts seed.shape.tiles = true) ∧
        mentsuCanonical seed.shape = true) ∧
        selectedIsCanonical seed = true := by
    simpa only [Seed.valid, Bool.and_eq_true] using valid
  have componentValid :
      (componentKindWithoutWait seed.wait
        (seed.shape.chunk seed.selected)).isSome = true := by
    exact validParts.1.1.1
  have waitMember := wait_mem_chunk_of_componentKind_isSome
    seed.wait (seed.shape.chunk seed.selected) componentValid
  apply List.mem_filter.mpr
  refine ⟨?_, valid⟩
  simp only [seedCandidates, List.mem_flatMap]
  refine ⟨seed.shape, mem_winningShapes seed.shape, seed.selected,
    mem_componentIndices seed.selected, ?_⟩
  apply List.mem_map.mpr
  exact ⟨seed.wait, List.mem_dedup.mpr waitMember, rfl⟩

/-- 直接生成器への所属と Reading の妥当性は一致する。 -/
theorem mem_directSeeds_iff {seed : Seed n} :
    seed ∈ directSeeds n ↔ seed.valid :=
  ⟨directSeeds_sound, directSeeds_complete⟩

/-- 妥当性証拠を付け、直接生成器の出力を Reading の集合として公開する。 -/
def directReadings (n : Nat) : List (Reading n) :=
  (directSeeds n).attach.map fun seed => ⟨seed.1, directSeeds_sound seed.2⟩

/-- すべての Reading は、全 Seed を走査しない直接生成器から得られる。 -/
theorem mem_directReadings (reading : Reading n) :
    reading ∈ directReadings n := by
  apply List.mem_map.mpr
  let generated : { seed // seed ∈ directSeeds n } :=
    ⟨reading.1, directSeeds_complete reading.2⟩
  refine ⟨generated, by simp [generated], ?_⟩
  apply Subtype.ext
  rfl

/-!
## 疎な構造コード

密な `Fin N` の順位ではなく、Seed を構成する直積を自然数へ符号化する。基礎要素の
`Tile`、`Toitsu`、`MentsuCandidate`、`ComponentIndex` だけは小さな有限型として符号表を
作るが、`Seed n` や `Reading n` 全体は列挙しない。コード値には未使用の自然数があるため
疎だが、`sparseCode_injective` により衝突しない。
-/

private def seedEquiv (n : Nat) :
    Seed n ≃ (Toitsu × (Fin n → MentsuCandidate)) × (ComponentIndex n × Tile) where
  toFun seed := ((seed.shape.pair, seed.shape.mentsu), (seed.selected, seed.wait))
  invFun value :=
    { shape := { pair := value.1.1, mentsu := value.1.2 }
      selected := value.2.1
      wait := value.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Seed 全体の列挙を避け、各フィールドを独立に符号化する構造的な `Encodable`。 -/
noncomputable def seedEncodable (n : Nat) : Encodable (Seed n) := by
  letI : Encodable Tile := Fintype.toEncodable Tile
  letI : Encodable Toitsu := Fintype.toEncodable Toitsu
  letI : Encodable MentsuCandidate := Fintype.toEncodable MentsuCandidate
  letI : Encodable (ComponentIndex n) := Fintype.toEncodable (ComponentIndex n)
  exact Encodable.ofEquiv _ (seedEquiv n)

/-- Reading の積構造を自然数へ写す疎なコード。 -/
noncomputable def sparseCode (reading : Reading n) : Nat :=
  @Encodable.encode (Seed n) (seedEncodable n) reading.1

/-- 疎な構造コードは衝突しない。 -/
theorem sparseCode_injective : Function.Injective (sparseCode (n := n)) := by
  intro first second equal
  apply Subtype.ext
  exact (@Encodable.encode_injective (Seed n) (seedEncodable n)) equal

/-- リストを牌種順に並べ、牌姿を多重集合の標準表現にする。 -/
def canonicalTiles (tiles : List Tile) : List Tile :=
  tiles.mergeSort fun first second => first.orderKey ≤ second.orderKey

/-- Reading から待ち牌を1枚除いて得られる `1 + 3n` 枚の牌姿。 -/
def hand (reading : Reading n) : List Tile :=
  canonicalTiles (reading.1.shape.tiles.erase reading.1.wait)

private theorem mem_shape_tiles_of_mem_chunk
    (shape : WinningShape n) (selected : ComponentIndex n) (tile : Tile)
    (member : tile ∈ (shape.chunk selected).tiles) :
    tile ∈ shape.tiles := by
  cases selected with
  | pair =>
      simp only [WinningShape.tiles, WinningShape.chunks, List.mem_flatMap]
      exact ⟨.inl shape.pair, List.mem_cons.mpr (Or.inl rfl), member⟩
  | mentsu index =>
      simp only [WinningShape.tiles, WinningShape.chunks, List.mem_flatMap]
      refine ⟨.inr (shape.mentsu index), ?_, member⟩
      simp only [List.mem_cons]
      right
      apply List.mem_map.mpr
      exact ⟨shape.mentsu index, List.mem_ofFn.mpr ⟨index, rfl⟩, rfl⟩

/--
生成した牌姿へ待ち牌を戻すと、元の雀頭と `n` 面子からなる和了形に戻る。

これは全牌姿を探索する計算ではなく、選択部品に待ち牌が含まれることと、リストから1要素を
消して戻す操作が順列を保つことだけから得られる semantic soundness である。
-/
theorem wait_cons_hand_perm_winningShape (reading : Reading n) :
    (reading.1.wait :: hand reading).Perm reading.1.shape.tiles := by
  have validParts :
      (((componentKindWithoutWait reading.1.wait
          (reading.1.shape.chunk reading.1.selected)).isSome = true ∧
        hasLegalTileCounts reading.1.shape.tiles = true) ∧
        mentsuCanonical reading.1.shape = true) ∧
        selectedIsCanonical reading.1 = true := by
    simpa only [Seed.valid, Bool.and_eq_true] using reading.2
  have waitInChunk := wait_mem_chunk_of_componentKind_isSome
    reading.1.wait (reading.1.shape.chunk reading.1.selected) validParts.1.1.1
  have waitInShape := mem_shape_tiles_of_mem_chunk
    reading.1.shape reading.1.selected reading.1.wait waitInChunk
  exact (List.mergeSort_perm _ _).cons reading.1.wait |>.trans
    (List.perm_cons_erase waitInShape).symm

/-- Reading に対応する待ち牌と完成分割。既存の探索器と接続するための表示である。 -/
def completion (reading : Reading n) : WaitCompletion :=
  { wait := reading.1.wait
    winningChunks := TileChunk.canonicalize reading.1.shape.chunks }

/-- `n` 面子 Reading の総数。完全ハッシュで使える自然数の上限でもある。 -/
abbrev readingCount (n : Nat) : Nat := Fintype.card (Reading n)

/--
有限添字から全 Reading への完全ハッシュ。実装上はこの関数で Reading を直接列挙し、
牌姿全体の列挙を避ける。
-/
noncomputable def readingEquiv (n : Nat) : Fin (readingCount n) ≃ Reading n :=
  (Fintype.equivFin (Reading n)).symm

/-- 完全ハッシュの順方向。 -/
noncomputable def ofIndex (index : Fin (readingCount n)) : Reading n :=
  readingEquiv n index

/-- Reading を完全ハッシュの添字へ戻す。 -/
noncomputable def toIndex (reading : Reading n) : Fin (readingCount n) :=
  (readingEquiv n).symm reading

/-- `ofIndex` は単射かつ全射であり、有効な各自然数がちょうど1つの Reading を表す。 -/
theorem ofIndex_bijective : Function.Bijective (ofIndex (n := n)) :=
  (readingEquiv n).bijective

@[simp] theorem toIndex_ofIndex (index : Fin (readingCount n)) :
    toIndex (ofIndex index) = index :=
  (readingEquiv n).symm_apply_apply index

@[simp] theorem ofIndex_toIndex (reading : Reading n) :
    ofIndex (toIndex reading) = reading :=
  (readingEquiv n).apply_symm_apply reading

/-- 指定した牌姿を生成する全 Reading。これがその牌姿の曖昧さの定義である。 -/
noncomputable def readingsForHand (tiles : List Tile) : Finset (Reading n) :=
  Finset.univ.filter fun reading => hand reading = canonicalTiles tiles

/-- `readingsForHand` は、指定牌姿へ射影される Reading をちょうど含む。 -/
theorem mem_readingsForHand_iff (reading : Reading n) (tiles : List Tile) :
    reading ∈ readingsForHand tiles ↔ hand reading = canonicalTiles tiles := by
  simp [readingsForHand]

/-- 牌姿が持つ異なる Reading の個数。1より大きければ待ちまたは分割が曖昧である。 -/
noncomputable def ambiguity (n : Nat) (tiles : List Tile) : Nat :=
  (readingsForHand (n := n) tiles).card

/-- 直接生成器の出力から、指定牌姿へ射影される Reading だけを集める。 -/
def directlyGeneratedReadingsForHand (tiles : List Tile) : Finset (Reading n) :=
  (directReadings n).toFinset.filter fun reading => hand reading = canonicalTiles tiles

/--
直接生成器は牌姿の曖昧さを過不足なく回収する。

左辺は選択部品に含まれる最大3種の待ち牌だけを試す実行用生成器、右辺は数学的に存在する
全 Reading から定義した牌姿のファイバーである。
-/
theorem directly_generated_readings_complete (tiles : List Tile) :
    directlyGeneratedReadingsForHand (n := n) tiles = readingsForHand tiles := by
  ext reading
  simp [directlyGeneratedReadingsForHand, readingsForHand, mem_directReadings]

/-- 完全ハッシュの全添字から、指定牌姿へ戻る Reading だけを集めたもの。 -/
noncomputable def indexedReadingsForHand (tiles : List Tile) : Finset (Reading n) :=
  ((Finset.univ : Finset (Fin (readingCount n))).filter fun index =>
      hand (ofIndex index) = canonicalTiles tiles).image ofIndex

/--
完全ハッシュを全走査して得る重複は、牌姿の曖昧さを完全にカバーする。

左辺は生成アルゴリズムが実際に集める集合、右辺は牌姿への射影の数学的なファイバーである。
両者の一致により、Reading の取りこぼしも、生成規則に由来しない余分な重複もない。
-/
theorem indexed_readings_complete (tiles : List Tile) :
    indexedReadingsForHand (n := n) tiles = readingsForHand tiles := by
  ext reading
  constructor
  · intro member
    simp only [indexedReadingsForHand, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and] at member
    obtain ⟨index, handMatches, rfl⟩ := member
    exact (mem_readingsForHand_iff _ _).mpr handMatches
  · intro member
    have handMatches := (mem_readingsForHand_iff reading tiles).mp member
    apply Finset.mem_image.mpr
    refine ⟨toIndex reading, ?_, ofIndex_toIndex reading⟩
    simp [handMatches]

/-- 通常手の範囲 `n = 0, ..., 4` にある全 Reading をまとめた有限型。 -/
abbrev StandardDirectWaitReading :=
  (n : Fin (standardHandMentsuCount + 1)) × Reading n.val

end DirectWaitReading
