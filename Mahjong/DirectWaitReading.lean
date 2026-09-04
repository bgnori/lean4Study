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
ことを示す。さらに `mem_findWaitCompletions_iff_exists_reading` は、既存 Finder の各結果と
通常手範囲の直接生成 Reading の存在が、牌姿のリスト順を正規化すれば同値であることを示す。
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

private def keysNondecreasing : List Nat → Bool
  | [] | [_] => true
  | first :: second :: rest => first ≤ second && keysNondecreasing (second :: rest)

private def mentsuOrderLE (first second : MentsuCandidate) : Bool :=
  decide (TileChunk.orderKey (.inr first) ≤ TileChunk.orderKey (.inr second))

private def canonicalMentsu (mentsu : List MentsuCandidate) : List MentsuCandidate :=
  mentsu.mergeSort mentsuOrderLE

private theorem keysNondecreasing_of_pairwise {keys : List Nat}
    (sorted : keys.Pairwise fun first second => decide (first ≤ second) = true) :
    keysNondecreasing keys = true := by
  induction keys with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil => rfl
      | cons second tail =>
          simp only [keysNondecreasing, Bool.and_eq_true]
          constructor
          · cases sorted with
            | cons head _ => exact head second (by simp)
          · exact inductionHypothesis sorted.tail

private theorem canonicalMentsu_keysNondecreasing (mentsu : List MentsuCandidate) :
    keysNondecreasing
      ((canonicalMentsu mentsu).map fun candidate => TileChunk.orderKey (.inr candidate)) =
      true := by
  apply keysNondecreasing_of_pairwise
  have sorted := List.pairwise_mergeSort
    (le := mentsuOrderLE) (by simp [mentsuOrderLE]; omega)
      (by simp [mentsuOrderLE, Nat.le_total]) mentsu
  apply List.Pairwise.map
    (fun candidate : MentsuCandidate => TileChunk.orderKey (.inr candidate))
    (fun _ _ relation => by simpa [mentsuOrderLE] using relation)
    sorted

private def mentsuCanonical (shape : WinningShape n) : Bool :=
  keysNondecreasing ((List.ofFn shape.mentsu).map fun mentsu =>
    TileChunk.orderKey (.inr mentsu))

private def selectedIsCanonical (seed : Seed n) : Bool :=
  match seed.selected with
  | .pair => true
  | .mentsu selected =>
      ((List.ofFn seed.shape.mentsu).take selected.val).all fun earlier =>
        earlier != seed.shape.mentsu selected

/--
直接生成パラメータの妥当性。

待ち牌が選択部品を実際に不完全形へ変え、完成形が4枚制限を守ることに加え、面子順と
同一面子の選択を正規化する。後者は、面子の並べ替えや同一面子の別の出現位置だけが違う
生成元を、別 Reading と誤って数えないために必要である。
-/
def Seed.valid (seed : Seed n) : Bool :=
  (componentKindAfterRemovingWait seed.wait (seed.shape.chunk seed.selected)).isSome &&
  decide (HasLegalTileCounts seed.shape.tiles) &&
  mentsuCanonical seed.shape &&
  selectedIsCanonical seed

/-- `n` 面子の完成形から直接生成できる、正規化済みの全 Reading。 -/
abbrev Reading (n : Nat) := { seed : Seed n // seed.valid }

private theorem wait_mem_chunk_of_componentKind_isSome
    (wait : Tile) (chunk : TileChunk)
    (valid : (componentKindAfterRemovingWait wait chunk).isSome = true) :
    wait ∈ chunk.tiles := by
  rcases chunk with pair | mentsu
  · rcases pair with ⟨tile⟩
    simp only [componentKindAfterRemovingWait] at valid
    split at valid
    · have tileEq : tile = wait := by simpa using ‹(tile == wait) = true›
      subst tile
      simp [TileChunk.tiles, Toitsu.tiles]
    · simp at valid
  · rcases mentsu with shuntsuPattern | tile
    · rcases shuntsuPattern with ⟨suit, start⟩
      cases wait with
      | honor honor => simp [componentKindAfterRemovingWait] at valid
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
                · simp [componentKindAfterRemovingWait, first, middle, last] at valid
          · simp [componentKindAfterRemovingWait, sameSuit] at valid
    · simp only [componentKindAfterRemovingWait] at valid
      split at valid
      · have tileEq : tile = wait := by simpa using ‹(tile == wait) = true›
        subst tile
        simp [TileChunk.tiles, MentsuCandidate.tiles]
      · simp at valid

private theorem componentKind_isSome_of_wait_mem
    (wait : Tile) (chunk : TileChunk) (member : wait ∈ chunk.tiles) :
    (componentKindAfterRemovingWait wait chunk).isSome = true := by
  rcases chunk with pair | mentsu
  · rcases pair with ⟨tile⟩
    simp [TileChunk.tiles, Toitsu.tiles] at member
    subst tile
    simp [componentKindAfterRemovingWait]
  · rcases mentsu with shuntsuPattern | tile
    · rcases shuntsuPattern with ⟨suit, start⟩
      cases wait with
      | honor honor => simp [TileChunk.tiles, MentsuCandidate.tiles, Shuntsu.tiles] at member
      | numbered waitSuit rank =>
          simp only [TileChunk.tiles, MentsuCandidate.tiles, Shuntsu.tiles,
            List.mem_cons] at member
          rcases member with first | middle | last | impossible
          · injection first with suitEq rankEq
            subst waitSuit
            subst rank
            simp [componentKindAfterRemovingWait]
          · injection middle with suitEq rankEq
            subst waitSuit
            subst rank
            simp only [componentKindAfterRemovingWait]
            rw [show (suit != suit) = false by simp]
            simp only [Bool.false_eq_true, ↓reduceIte]
            split <;> simp
          · injection last with suitEq rankEq
            subst waitSuit
            subst rank
            simp only [componentKindAfterRemovingWait]
            rw [show (suit != suit) = false by simp]
            simp only [Bool.false_eq_true, ↓reduceIte]
            split
            · simp
            · split <;> simp
          · contradiction
    · simp [TileChunk.tiles, MentsuCandidate.tiles] at member
      subst tile
      simp [componentKindAfterRemovingWait]

/-!
## 直接生成器

`Fintype` から `Seed n` 全体を列挙すると、待ち牌について常に34種類を試すことになる。
さらに、有限関数全体を一度に `Finset` 化すると大きな中間データ構造が必要になる。
以下では面子関数をリストとして再帰生成し、完成形と選択部品を選んだ後、待ち牌候補を
その部品に実際に含まれる最大3種類へ限定する。
-/

/-- `n` 個の完成面子の全列。全関数の `Finset` を構築せず、先頭追加で生成する。 -/
def mentsuFunctions : (n : Nat) → List (Fin n → MentsuCandidate)
  | 0 => [fun index => Fin.elim0 index]
  | n + 1 =>
      MentsuCandidate.candidates.flatMap fun first =>
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
      refine ⟨mentsu 0, MentsuCandidate.mem_candidates (mentsu 0), ?_⟩
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

/--
`directSeeds` が列挙したすべての `Seed` は、物理制約と正規化条件をまとめた `Seed.valid` を満たす。

`directSeeds` は `seedCandidates` を `seed.valid` で `filter` した列なので、所属証拠を
`List.mem_filter.mp` で分解すれば、フィルタ条件が真であるという証拠をそのまま取り出せる。
これは直接生成器が不正なReadingの生成元を返さないという健全性を保証する。

読むためのLean語彙: 健全性, `List.filter`, `List.mem_filter`, `.mp`, `.2`。
-/
theorem directSeeds_sound {seed : Seed n} (member : seed ∈ directSeeds n) :
    seed.valid := by
  exact (List.mem_filter.mp member).2

/--
`Seed.valid` を満たすすべての `Seed` は、`directSeeds` の出力に含まれる。

候補生成は、全完成形、全部品位置、選択部品に含まれる全牌種の3段階からなる。最初の2段階は
`mem_winningShapes` と `mem_componentIndices` により任意の `seed.shape` と `seed.selected` を含む。
3段階目については、`Seed.valid` の最初の条件から、待ち牌を除く処理が成功することを取り出す。
`wait_mem_chunk_of_componentKind_isSome` により `seed.wait` が選択部品に含まれると分かるため、
`dedup` と `map` を通った候補列にも元の `seed` が含まれる。最後に元の妥当性証拠をフィルタ条件として戻す。

したがって、候補を選択部品内の最大3牌種へ限定する最適化を行っても、妥当なSeedを取りこぼさない。
これは直接生成器の完全性を保証する。

読むためのLean語彙: 完全性, `Bool.and_eq_true`, `List.mem_flatMap`, `List.mem_map`,
`List.mem_dedup`, `List.mem_filter`, `refine`。
-/
theorem directSeeds_complete {seed : Seed n} (valid : seed.valid) :
    seed ∈ directSeeds n := by
  have validParts :
      (((componentKindAfterRemovingWait seed.wait
          (seed.shape.chunk seed.selected)).isSome = true ∧
        decide (HasLegalTileCounts seed.shape.tiles) = true) ∧
        mentsuCanonical seed.shape = true) ∧
        selectedIsCanonical seed = true := by
    simpa only [Seed.valid, Bool.and_eq_true] using valid
  have componentValid :
      (componentKindAfterRemovingWait seed.wait
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

/--
`Seed` が直接生成器の出力に含まれることと、その `Seed` が妥当であることは同値である。

`directSeeds_sound` と `directSeeds_complete` をそれぞれ同値の両方向として組み合わせる。
この定理が、実行可能な直接生成器と宣言的な妥当性条件の境界になる。
-/
theorem mem_directSeeds_iff {seed : Seed n} :
    seed ∈ directSeeds n ↔ seed.valid :=
  ⟨directSeeds_sound, directSeeds_complete⟩

example :
    let seed : Seed 0 :=
      { shape :=
          { pair := .toitsu (.honor .Red)
            mentsu := fun index => Fin.elim0 index }
        selected := .pair
        wait := .honor .Red }
    seed ∈ directSeeds 0 := by
  dsimp
  apply directSeeds_complete
  native_decide

/--
`directSeeds` の各要素に妥当性証拠を付け、同じ生成結果を `Reading` の列として公開する。

`attach` が各Seedに `directSeeds n` への所属証拠を付け、`directSeeds_sound` がその証拠を
`Seed.valid` の証拠へ変換する。Seed自体を選別し直す処理ではない。
-/
def directReadings (n : Nat) : List (Reading n) :=
  (directSeeds n).attach.map fun seed => ⟨seed.1, directSeeds_sound seed.2⟩

/--
すべての `Reading` は、全Seedを走査しない `directReadings` に含まれる。

`Reading n` は、Seed本体 `reading.1` と妥当性証拠 `reading.2` を持つ部分型である。
`directSeeds_complete reading.2` によりSeed本体が `directSeeds n` に含まれると分かるので、
その値と所属証拠の組 `generated` は `attach` 後の列に含まれる。`map` が付け直す妥当性証拠は
元の `reading.2` と同じ証明項である必要はないため、最後は `Subtype.ext` でSeed本体だけを比較する。

したがって、実行用の列挙は宣言的に定義された任意のReadingを取りこぼさない。

読むためのLean語彙: 部分型, `List.attach`, `List.mem_map`, `Subtype.ext`。
-/
theorem mem_directReadings (reading : Reading n) :
    reading ∈ directReadings n := by
  apply List.mem_map.mpr
  let generated : { seed // seed ∈ directSeeds n } :=
    ⟨reading.1, directSeeds_complete reading.2⟩
  refine ⟨generated, by simp [generated], ?_⟩
  apply Subtype.ext
  rfl

example :
    let seed : Seed 0 :=
      { shape :=
          { pair := .toitsu (.honor .Red)
            mentsu := fun index => Fin.elim0 index }
        selected := .pair
        wait := .honor .Red }
    let reading : Reading 0 := ⟨seed, by native_decide⟩
    reading ∈ directReadings 0 := by
  dsimp only
  exact mem_directReadings _

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
private def tileOrderLE (first second : Tile) : Bool :=
  decide (first.orderKey ≤ second.orderKey)

def canonicalTiles (tiles : List Tile) : List Tile :=
  tiles.mergeSort tileOrderLE

private theorem canonicalTiles_eq_of_perm {first second : List Tile}
    (permutation : first.Perm second) :
    canonicalTiles first = canonicalTiles second := by
  apply List.Perm.eq_of_pairwise (le := fun a b => a.orderKey ≤ b.orderKey)
  · intro a b _ _ firstLe secondLe
    have keyEq : a.orderKey = b.orderKey := by omega
    have : Function.Injective Tile.orderKey := by native_decide
    exact this keyEq
  · simpa [canonicalTiles, tileOrderLE] using List.pairwise_mergeSort
      (le := tileOrderLE) (by simp [tileOrderLE]; omega)
        (by simp [tileOrderLE, Nat.le_total]) first
  · simpa [canonicalTiles, tileOrderLE] using List.pairwise_mergeSort
      (le := tileOrderLE) (by simp [tileOrderLE]; omega)
        (by simp [tileOrderLE, Nat.le_total]) second
  · exact (List.mergeSort_perm _ _).trans
      (permutation.trans (List.mergeSort_perm _ _).symm)

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

ここで「戻る」はリストとして同じ順番になることではなく、同じ牌を同じ枚数だけ持つ `List.Perm` を意味する。
`hand` は待ち牌を除いた後に牌種順へ整列するため、元の完成形とは並び順が異なり得るからである。

証明ではまず、`Seed.valid` の「選択部品から待ち牌を除ける」という条件から、待ち牌が選択部品に含まれることを
得る。`mem_shape_tiles_of_mem_chunk` でその所属を完成形全体へ持ち上げると、`List.perm_cons_erase` により
待ち牌を除いて再び先頭へ加えた列が元の完成形の順列だと分かる。さらに `List.mergeSort_perm` により、
`hand` が行う整列も牌と重複数を変えないことをつなぐ。

したがって `hand` は、不正な牌を作ったり必要な牌を失ったりせず、完成形から待ち牌をちょうど1枚除いた
テンパイ牌姿を表す。この保存則は、後でReadingを既存の待ち判定とFinderへ接続する根拠になる。

読むためのLean語彙: `List.erase`, `List.Perm`, `List.mergeSort_perm`,
`List.perm_cons_erase`, `.trans`, `.symm`。
-/
theorem wait_cons_hand_perm_winningShape (reading : Reading n) :
    (reading.1.wait :: hand reading).Perm reading.1.shape.tiles := by
  have validParts :
      (((componentKindAfterRemovingWait reading.1.wait
          (reading.1.shape.chunk reading.1.selected)).isSome = true ∧
        decide (HasLegalTileCounts reading.1.shape.tiles) = true) ∧
        mentsuCanonical reading.1.shape = true) ∧
        selectedIsCanonical reading.1 = true := by
    simpa only [Seed.valid, Bool.and_eq_true] using reading.2
  have waitInChunk := wait_mem_chunk_of_componentKind_isSome
    reading.1.wait (reading.1.shape.chunk reading.1.selected) validParts.1.1.1
  have waitInShape := mem_shape_tiles_of_mem_chunk
    reading.1.shape reading.1.selected reading.1.wait waitInChunk
  exact (List.mergeSort_perm _ _).cons reading.1.wait |>.trans
    (List.perm_cons_erase waitInShape).symm

example :
    let seed : Seed 0 :=
      { shape :=
          { pair := .toitsu (.honor .Red)
            mentsu := fun index => Fin.elim0 index }
        selected := .pair
        wait := .honor .Red }
    let reading : Reading 0 := ⟨seed, by native_decide⟩
    (reading.1.wait :: hand reading).Perm reading.1.shape.tiles := by
  native_decide

private theorem mentsuChunk_tiles_length (mentsu : MentsuCandidate) :
  (TileChunk.tiles (.inr mentsu)).length = mentsuTileCount := by
  cases mentsu with
  | shuntsu shuntsuPattern =>
      cases shuntsuPattern
      rfl
  | koutsu tile => rfl

private theorem mentsuChunks_tiles_length (mentsu : List MentsuCandidate) :
    ((mentsu.map fun candidate => (Sum.inr candidate : TileChunk)).flatMap
      TileChunk.tiles).length = mentsu.length * mentsuTileCount := by
  induction mentsu with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [List.map_cons, List.flatMap_cons, List.length_append]
      rw [mentsuChunk_tiles_length, inductionHypothesis]
      simp [Nat.add_mul, Nat.add_comm]

private theorem winningShape_tiles_length (shape : WinningShape n) :
    shape.tiles.length = n * mentsuTileCount + 2 := by
  have restLength := mentsuChunks_tiles_length (List.ofFn shape.mentsu)
  simp only [WinningShape.tiles, WinningShape.chunks, List.flatMap_cons,
    List.length_append]
  rw [restLength]
  simp [TileChunk.tiles, Toitsu.tiles, Nat.add_comm]

private theorem winningShape_partition (shape : WinningShape n) :
    WinningPartition shape.tiles shape.chunks := by
  let rest : List TileChunk :=
    (List.ofFn shape.mentsu).map fun candidate => (Sum.inr candidate : TileChunk)
  have allMentsu : ∀ chunk ∈ rest, chunk ∈ mentsuChunkCandidates := by
    intro chunk member
    obtain ⟨candidate, _, rfl⟩ := List.mem_map.mp member
    exact mentsu_mem_mentsuChunkCandidates candidate
  have tail := mentsuPartition_flatMap rest allMentsu
  have restLength : rest.length = n := by simp [rest]
  have remainingLength :
      (rest.flatMap TileChunk.tiles).length = n * mentsuTileCount := by
    simpa [rest] using mentsuChunks_tiles_length (List.ofFn shape.mentsu)
  rw [restLength] at tail
  have fuelEq : (rest.flatMap TileChunk.tiles).length / mentsuTileCount = n := by
    rw [remainingLength]
    simp [mentsuTileCount]
  rw [← fuelEq] at tail
  have removePair :
      removeTiles shape.tiles (TileChunk.tiles (.inl shape.pair)) =
        some (rest.flatMap TileChunk.tiles) := by
    simpa [WinningShape.tiles, WinningShape.chunks, rest] using
      removeTiles_append_left (TileChunk.tiles (.inl shape.pair))
        (rest.flatMap TileChunk.tiles)
  exact .intro (.inl shape.pair) (pair_mem_pairChunkCandidates shape.pair)
    removePair tail

private theorem hasLegalTileCounts_of_valid (reading : Reading n) :
    HasLegalTileCounts reading.1.shape.tiles := by
  have validParts :
      (((componentKindAfterRemovingWait reading.1.wait
          (reading.1.shape.chunk reading.1.selected)).isSome = true ∧
        decide (HasLegalTileCounts reading.1.shape.tiles) = true) ∧
        mentsuCanonical reading.1.shape = true) ∧
        selectedIsCanonical reading.1 = true := by
    simpa only [Seed.valid, Bool.and_eq_true] using reading.2
  exact of_decide_eq_true validParts.1.1.2

private theorem reading_waitFor (reading : Reading n) (standard : n ≤ standardHandMentsuCount) :
    IsWaitFor (hand reading) reading.1.wait := by
  have permutation := wait_cons_hand_perm_winningShape reading
  have partition : WinningPartition (reading.1.wait :: hand reading) reading.1.shape.chunks :=
    (winningShape_partition reading.1.shape).of_perm permutation.symm
  have partitionMember :=
    (mem_winningPartitions_iff _ _).mpr partition
  have shapeLegal := hasLegalTileCounts_of_valid reading
  have countEq := permutation.count reading.1.wait
  have lengthEq := permutation.length_eq
  constructor
  · constructor
    · unfold IsTenpaiHandSize
      rw [winningShape_tiles_length reading.1.shape] at lengthEq
      simp only [List.length_cons] at lengthEq
      simp [mentsuTileCount] at lengthEq
      simp [standardHandMentsuCount] at standard
      omega
    · intro tile
      have tileCountEq := permutation.count tile
      have shapeCount := shapeLegal tile
      by_cases same : tile = reading.1.wait
      · subst tile
        simp at tileCountEq
        omega
      · have reverseDifferent : reading.1.wait ≠ tile := Ne.symm same
        have different : (reading.1.wait == tile) = false := by
          simp [reverseDifferent]
        simp only [List.count_cons, different] at tileCountEq
        omega
  · constructor
    · have waitCount := shapeLegal reading.1.wait
      simp only [List.count_cons, beq_self_eq_true, ite_true] at countEq
      omega
    · unfold IsStandardAgari isWinning
      have nonempty : winningPartitions (reading.1.wait :: hand reading) ≠ [] :=
        List.ne_nil_of_mem partitionMember
      simp [nonempty]

/-- Reading に対応する待ち牌と完成分割。既存の探索器と接続するための表示である。 -/
def completion (reading : Reading n) : WaitCompletion :=
  { wait := reading.1.wait
    winningChunks := TileChunk.canonicalize reading.1.shape.chunks }

/--
通常手範囲の直接生成Readingは、同じ牌姿に対する既存Finderの出力に必ず現れる。

`standard` は面子数 `n` が通常手の上限4以下であることを表す。この範囲では `reading_waitFor` が、
生成した `hand reading` に対して `reading.1.wait` が実際の待ち牌であることを保証する。
また `winningShape_partition` が元の完成形の分割を与え、`wait_cons_hand_perm_winningShape` と
`WinningPartition.of_perm` により、その分割を「待ち牌を生成牌姿へ加えた列」へ移す。

この待ちの証拠と完成分割の証拠を `mem_findWaitCompletions_iff` の仕様側へ渡すことで、
`completion reading` が探索結果に含まれると結論する。したがって直接生成器は、既存Finderから見ても
根拠のない待ちや分割を作らない。

読むためのLean語彙: `IsWaitFor`, `WinningPartition`, `mem_findWaitCompletions_iff`,
`.mpr`, `WinningPartition.of_perm`。
-/
theorem completion_mem_findWaitCompletions (reading : Reading n)
    (standard : n ≤ standardHandMentsuCount) :
    completion reading ∈ findWaitCompletions (hand reading) := by
  apply (mem_findWaitCompletions_iff _ _).mpr
  exact .intro reading.1.wait reading.1.shape.chunks
    (reading_waitFor reading standard)
    ((winningShape_partition reading.1.shape).of_perm
      (wait_cons_hand_perm_winningShape reading).symm)

example (reading : Reading 0) :
    completion reading ∈ findWaitCompletions (hand reading) := by
  exact completion_mem_findWaitCompletions reading (by omega)

private theorem legal_cons_of_waitFor {tiles : List Tile} {wait : Tile}
    (waitFor : IsWaitFor tiles wait) : HasLegalTileCounts (wait :: tiles) := by
  intro tile
  rcases waitFor with ⟨⟨_, legal⟩, waitCount, _⟩
  by_cases same : tile = wait
  · subst tile
    simp
    omega
  · have reverseDifferent : wait ≠ tile := Ne.symm same
    simp [reverseDifferent, legal tile]

private theorem legalTileCounts_decide_eq_true_of_perm {first second : List Tile}
    (permutation : first.Perm second) (legal : HasLegalTileCounts second) :
    decide (HasLegalTileCounts first) = true := by
  apply decide_eq_true
  intro tile
  simpa [permutation.count tile] using legal tile

private theorem selectedCanonical_at_idxOf {candidate : MentsuCandidate}
    {mentsu : List MentsuCandidate} (member : candidate ∈ mentsu) :
    ((mentsu.take (mentsu.idxOf candidate)).all fun earlier => earlier != candidate) = true := by
  apply List.all_eq_true.mpr
  intro earlier earlierMember
  have earlierNe : earlier ≠ candidate := by
    intro equal
    subst earlier
    exact Nat.lt_irrefl _ ((List.mem_take_iff_idxOf_lt member).mp earlierMember)
  simp [earlierNe]

/--
既存 Finder が返す各 completion には、それと同じ牌姿・待ち牌・正規化分割を持つ
直接生成 Reading が存在する。面子数は Finder の分割から復元する。
-/
theorem exists_reading_of_mem_findWaitCompletions {tiles : List Tile}
    {found : WaitCompletion} (member : found ∈ findWaitCompletions tiles) :
    ∃ n, ∃ reading : Reading n,
  n ≤ standardHandMentsuCount ∧
  hand reading = canonicalTiles tiles ∧ completion reading = found := by
  have completionFor := (mem_findWaitCompletions_iff tiles found).mp member
  cases completionFor with
  | intro wait rawChunks waitFor partition =>
      cases partition with
      | intro pairChunk pairCandidate removePair mentsuPartition =>
        rename_i remaining rest
        obtain ⟨pair, rfl⟩ := pair_of_mem_pairChunkCandidates pairCandidate
        obtain ⟨rawMentsu, restEq⟩ := mentsuPartition.exists_candidates
        subst rest
        let sorted := canonicalMentsu rawMentsu
        let shape : WinningShape sorted.length :=
          { pair
            mentsu := sorted.get }
        have shapeMentsu : List.ofFn shape.mentsu = sorted := by
          exact List.ofFn_get sorted
        have sortedPerm : sorted.Perm rawMentsu :=
          List.mergeSort_perm _ _
        have chunksPerm : shape.chunks.Perm
            (.inl pair :: rawMentsu.map fun candidate => (Sum.inr candidate : TileChunk)) := by
          simp only [WinningShape.chunks, shapeMentsu]
          exact List.Perm.cons (.inl pair)
            (sortedPerm.map fun candidate => (Sum.inr candidate : TileChunk))
        have rawTilesPerm :
            ((.inl pair : TileChunk) :: rawMentsu.map fun candidate =>
              (Sum.inr candidate : TileChunk)).flatMap TileChunk.tiles |>.Perm
                (wait :: tiles) := by
          have withPair := List.Perm.append_left (TileChunk.tiles (.inl pair))
            mentsuPartition.tiles_perm
          exact withPair.trans
            ((exists_removeTiles_eq_some_iff_perm (wait :: tiles)
              (TileChunk.tiles (.inl pair)) remaining).mp
              ⟨remaining, removePair, .refl remaining⟩)
        have shapeTilesPerm : shape.tiles.Perm (wait :: tiles) := by
          exact (chunksPerm.flatMap fun _ _ => .refl _).trans rawTilesPerm
        have shapeLegal : decide (HasLegalTileCounts shape.tiles) = true :=
          legalTileCounts_decide_eq_true_of_perm shapeTilesPerm
            (legal_cons_of_waitFor waitFor)
        have standard : sorted.length ≤ standardHandMentsuCount := by
          have legalSize := waitFor.1.1
          have lengthEq := shapeTilesPerm.length_eq
          rw [winningShape_tiles_length shape] at lengthEq
          simp only [List.length_cons] at lengthEq
          simp [mentsuTileCount, standardHandMentsuCount] at lengthEq ⊢
          rcases legalSize with one | four | seven | ten | thirteen <;> omega
        have waitInRaw : wait ∈
            ((.inl pair : TileChunk) :: rawMentsu.map fun candidate =>
              (Sum.inr candidate : TileChunk)).flatMap TileChunk.tiles :=
          rawTilesPerm.mem_iff.mpr (by simp)
        by_cases waitInPair : wait ∈ (TileChunk.tiles (.inl pair))
        · let seed : Seed sorted.length :=
            { shape
              selected := .pair
              wait }
          have seedValid : seed.valid := by
            simp only [Seed.valid, Bool.and_eq_true]
            refine ⟨⟨⟨componentKind_isSome_of_wait_mem wait (.inl pair) waitInPair,
              shapeLegal⟩, ?_⟩, rfl⟩
            change mentsuCanonical shape = true
            unfold mentsuCanonical
            change keysNondecreasing
              ((List.ofFn shape.mentsu).map fun candidate =>
                TileChunk.orderKey (.inr candidate)) = true
            rw [shapeMentsu]
            exact canonicalMentsu_keysNondecreasing rawMentsu
          let reading : Reading sorted.length := ⟨seed, seedValid⟩
          refine ⟨sorted.length, reading, standard, ?_, ?_⟩
          · apply canonicalTiles_eq_of_perm
            exact (List.Perm.erase wait shapeTilesPerm).trans
              (List.Perm.cons_inv (List.perm_cons_erase (by simp)).symm)
          · unfold completion
            congr 1
            exact TileChunk.canonicalize_eq_of_perm chunksPerm
        · have waitInMentsu : wait ∈
              (rawMentsu.map fun candidate => (Sum.inr candidate : TileChunk)).flatMap
                TileChunk.tiles := by
            simpa [waitInPair] using waitInRaw
          obtain ⟨chunk, chunkMember, waitInChunk⟩ := List.mem_flatMap.mp waitInMentsu
          obtain ⟨candidate, candidateMember, chunkEq⟩ := List.mem_map.mp chunkMember
          subst chunk
          have candidateSorted : candidate ∈ sorted :=
            List.mem_mergeSort.mpr candidateMember
          let selectedValue : Nat := sorted.idxOf candidate
          have selectedLt : selectedValue < sorted.length :=
            List.idxOf_lt_length_iff.mpr candidateSorted
          let selected : Fin sorted.length := ⟨selectedValue, selectedLt⟩
          have selectedEq : shape.mentsu selected = candidate := by
            exact List.getElem_idxOf selectedLt
          let seed : Seed sorted.length :=
            { shape
              selected := .mentsu selected
              wait }
          have seedValid : seed.valid := by
            simp only [Seed.valid, Bool.and_eq_true]
            refine ⟨⟨⟨?_, shapeLegal⟩, ?_⟩, ?_⟩
            · change (componentKindAfterRemovingWait wait
                (.inr (shape.mentsu selected))).isSome = true
              rw [selectedEq]
              exact componentKind_isSome_of_wait_mem wait (.inr candidate) waitInChunk
            · change keysNondecreasing
                ((List.ofFn shape.mentsu).map fun value =>
                  TileChunk.orderKey (.inr value)) = true
              rw [shapeMentsu]
              exact canonicalMentsu_keysNondecreasing rawMentsu
            · change selectedIsCanonical
                { shape := shape, selected := .mentsu selected, wait := wait } = true
              simp only [selectedIsCanonical]
              rw [shapeMentsu, selectedEq]
              change ((sorted.take (sorted.idxOf candidate)).all fun earlier =>
                earlier != candidate) = true
              exact selectedCanonical_at_idxOf candidateSorted
          let reading : Reading sorted.length := ⟨seed, seedValid⟩
          refine ⟨sorted.length, reading, standard, ?_, ?_⟩
          · apply canonicalTiles_eq_of_perm
            exact (List.Perm.erase wait shapeTilesPerm).trans
              (List.Perm.cons_inv (List.perm_cons_erase (by simp)).symm)
          · unfold completion
            congr 1
            exact TileChunk.canonicalize_eq_of_perm chunksPerm

/--
既存 Finder の出力と直接生成 Reading は、牌姿のリスト順を正規化すれば完全に同値である。

右辺は牌姿全体を列挙せず、1つの Reading とその通常手範囲の証拠だけを要求する。
-/
theorem mem_findWaitCompletions_iff_exists_reading
    (tiles : List Tile) (found : WaitCompletion) :
    found ∈ findWaitCompletions tiles ↔
      ∃ n, ∃ reading : Reading n,
        n ≤ standardHandMentsuCount ∧
        hand reading = canonicalTiles tiles ∧ completion reading = found := by
  constructor
  · exact exists_reading_of_mem_findWaitCompletions
  · rintro ⟨n, reading, standard, handEq, rfl⟩
    have generated := completion_mem_findWaitCompletions reading standard
    have generatedMeaning := (mem_findWaitCompletions_iff _ _).mp generated
    apply (mem_findWaitCompletions_iff _ _).mpr
    apply generatedMeaning.of_perm
    rw [handEq]
    exact List.mergeSort_perm _ _

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
