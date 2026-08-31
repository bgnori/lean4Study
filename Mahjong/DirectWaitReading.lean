import Mahjong.WaitReadingCode
import Mathlib.Data.Fintype.Pi

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

`readingEquiv` は有限型に標準で存在する完全ハッシュであり、自然数の有効範囲
`Fin (Fintype.card (Reading n))` と全 Reading の全単射を与える。

同じ牌姿へ射影される異なる Reading は、異なる待ち牌や和了分割に由来する曖昧さである。
`readingsForHand` をこの射影のファイバーとして定義し、`indexed_readings_complete` により、
完全ハッシュの全添字を調べればその曖昧さを過不足なく回収できることを示す。
-/

namespace DirectWaitReading

open WaitCompletionFinder
open WaitReadingCode

variable {n : Nat}

/-- 完成形のどの部品から待ち牌を取り除くか。 -/
inductive ComponentIndex (n : Nat)
| pair
| meld (index : Fin n)
deriving BEq, DecidableEq, Fintype, Repr

/-- 雀頭1個と `n` 個の面子からなる `2 + 3n` 枚の通常和了形。 -/
structure WinningShape (n : Nat) where
  pair : Toitsu
  melds : Fin n → MentsuCandidate
deriving BEq, DecidableEq, Fintype

namespace WinningShape

/-- 完成形の指定された部品を取り出す。 -/
def chunk (shape : WinningShape n) : ComponentIndex n → TileChunk
  | .pair => .inl shape.pair
  | .meld index => .inr (shape.melds index)

/-- 雀頭を先頭に置いた完成部品列。 -/
def chunks (shape : WinningShape n) : List TileChunk :=
  .inl shape.pair :: (List.ofFn shape.melds).map fun meld => (.inr meld : TileChunk)

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

private def meldsCanonical (shape : WinningShape n) : Bool :=
  keysNondecreasing ((List.ofFn shape.melds).map fun meld =>
    chunkOrderKey (.inr meld))

private def selectedIsCanonical (seed : Seed n) : Bool :=
  match seed.selected with
  | .pair => true
  | .meld selected =>
      ((List.ofFn seed.shape.melds).take selected.val).all fun earlier =>
        earlier != seed.shape.melds selected

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
  meldsCanonical seed.shape &&
  selectedIsCanonical seed

/-- `n` 面子の完成形から直接生成できる、正規化済みの全 Reading。 -/
abbrev Reading (n : Nat) := { seed : Seed n // seed.valid }

/-- リストを牌種順に並べ、牌姿を多重集合の標準表現にする。 -/
def canonicalTiles (tiles : List Tile) : List Tile :=
  tiles.mergeSort fun first second => first.orderKey ≤ second.orderKey

/-- Reading から待ち牌を1枚除いて得られる `1 + 3n` 枚の牌姿。 -/
def hand (reading : Reading n) : List Tile :=
  canonicalTiles (reading.1.shape.tiles.erase reading.1.wait)

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
