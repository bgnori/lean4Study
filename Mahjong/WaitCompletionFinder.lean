import Mahjong.WaitCompletion

/-!
# 待ちと和了分割の探索

`IsStandardAgari`、`IsWaitFor`、`IsTenpai` が通常形の意味論を定め、
`Wait tiles` が聴牌牌列 `tiles` に結び付いた待ちの証拠を表す。
`waitingTiles` は実際の待ち牌を計算する決定手続きであり、`findWaitCompletions` は、
待ち牌を加えた和了形をチャンクへ分解して得られる集合に対して正規化を行う。

このモジュールは物理牌ではなく、牌種 `Tile` のリストを対象にする。重複はリスト内の
出現回数で表す。`waitingTiles` は手牌枚数を1、4、7、10、13枚に限定し、
すべての牌種が4枚以下であることを確認してから探索する。
-/
namespace WaitCompletionFinder

/-- `available` から `wanted` の牌種列を多重集合的に取り除く。 -/
def removeTiles : List Tile → List Tile → Option (List Tile)
  | available, [] => some available
  | available, wanted :: rest =>
      if available.contains wanted then
        removeTiles (available.erase wanted) rest
      else
        none

/-- 雀頭候補として使う全牌種の対子。 -/
def pairChunkCandidates : List TileChunk :=
  Tile.all.map .pair

/-- 完成面子候補。全順子候補と全刻子候補を含む。 -/
def meldChunkCandidates : List TileChunk :=
  (Suit.all.flatMap fun suit =>
    List.ofFn fun start : ShuntsuStart =>
      TileChunk.shuntsu suit start) ++
  Tile.all.map .koutsu

/-- 牌種リストを完成面子だけに分解する。`fuel` は残り面子数の上限として使う。 -/
def decomposeMelds : Nat → List Tile → List (List TileChunk)
  | 0, tiles =>
      if tiles.isEmpty then [[]] else []
  | fuel + 1, tiles =>
      List.flatten (meldChunkCandidates.map fun meld =>
        match removeTiles tiles meld.tiles with
        | some remaining =>
            (decomposeMelds fuel remaining).map fun winningChunks => meld :: winningChunks
        | none => [])

/-- 牌種リストを雀頭1つと完成面子列に分解する。 -/
def winningPartitions (tiles : List Tile) : List (List TileChunk) :=
  List.flatten (pairChunkCandidates.map fun pairChunk =>
    match removeTiles tiles pairChunk.tiles with
    | some remaining =>
        (decomposeMelds (remaining.length / mentsuTileCount) remaining).map fun winningChunks =>
          pairChunk :: winningChunks
    | none => [])

/-- 牌種リストが通常形の和了形として分解できるか。 -/
def isWinning (tiles : List Tile) : Bool :=
  !(winningPartitions tiles).isEmpty

/-- 通常形聴牌として扱う手牌枚数。 -/
def IsTenpaiHandSize (size : Nat) : Prop :=
  size = 1 ∨ size = 4 ∨ size = 7 ∨ size = 10 ∨ size = 13

/-- 各牌種が物理的な上限枚数を超えていないこと。 -/
def HasLegalTileCounts (tiles : List Tile) : Prop :=
  ∀ tile, tiles.count tile ≤ copiesPerTile

/-- 待ち判定へ渡せる牌種列であること。 -/
def IsLegalTenpaiHand (tiles : List Tile) : Prop :=
  IsTenpaiHandSize tiles.length ∧ HasLegalTileCounts tiles

instance (size : Nat) : Decidable (IsTenpaiHandSize size) := by
  unfold IsTenpaiHandSize
  infer_instance

instance (tiles : List Tile) : Decidable (HasLegalTileCounts tiles) :=
  Fintype.decidableForallFintype

instance (tiles : List Tile) : Decidable (IsLegalTenpaiHand tiles) := by
  unfold IsLegalTenpaiHand
  infer_instance

/-- 牌種列が通常形（雀頭1つと完成面子列）の和了形であること。 -/
def IsStandardAgari (tiles : List Tile) : Prop :=
  isWinning tiles = true

/-- 有効な聴牌手に `candidate` を1枚加えると通常形で和了し、5枚目にもならないこと。 -/
def IsWaitFor (tiles : List Tile) (candidate : Tile) : Prop :=
  IsLegalTenpaiHand tiles ∧
    tiles.count candidate < copiesPerTile ∧
    IsStandardAgari (candidate :: tiles)

/-- 牌種列が少なくとも1種類の通常形待ちを持つこと。 -/
def IsTenpai (tiles : List Tile) : Prop :=
  ∃ candidate, IsWaitFor tiles candidate

/-- 手牌に結び付いた通常形待ちの証拠。 -/
structure Wait (tiles : List Tile) where
  tile : Tile
  valid : IsWaitFor tiles tile

/-- 与えられた聴牌形に対し、加えると通常形で和了になる牌種を列挙する。 -/
def waitingTiles (tiles : List Tile) : List Tile :=
  if IsLegalTenpaiHand tiles then
    Tile.all.filter fun candidate =>
      (tiles.count candidate < copiesPerTile) && isWinning (candidate :: tiles)
  else
    []

/-- `waitingTiles` は `IsWaitFor` をちょうど判定する。 -/
theorem mem_waitingTiles_iff (tiles : List Tile) (candidate : Tile) :
    candidate ∈ waitingTiles tiles ↔ IsWaitFor tiles candidate := by
  by_cases legal : IsLegalTenpaiHand tiles
  · simp [waitingTiles, legal, Tile.mem_all, IsWaitFor, IsStandardAgari,
      Bool.and_eq_true]
  · simp [waitingTiles, legal, IsWaitFor]

/-- `waitingTiles` が空でないことと意味論上の聴牌は同値である。 -/
theorem waitingTiles_ne_nil_iff (tiles : List Tile) :
    waitingTiles tiles ≠ [] ↔ IsTenpai tiles := by
  constructor
  · intro nonempty
    obtain ⟨candidate, member⟩ := List.exists_mem_of_ne_nil _ nonempty
    exact ⟨candidate, (mem_waitingTiles_iff tiles candidate).mp member⟩
  · rintro ⟨candidate, valid⟩ empty
    have member := (mem_waitingTiles_iff tiles candidate).mpr valid
    simp [empty] at member

/-- 待ち牌と、その待ち牌を加えた和了形の正規化済み分割を列挙する。 -/
def findWaitCompletions (tiles : List Tile) : List WaitCompletion :=
  ((waitingTiles tiles).flatMap fun wait =>
    (winningPartitions (wait :: tiles)).map fun winningChunks =>
      { wait, winningChunks := TileChunk.canonicalize winningChunks }).eraseDups

/-!
## 分解に関する既約性

`waitCompletionCount` は待ち牌と和了形の組を数える。メンツを1つ除いた
聴牌形が同じ個数の分解を持つなら、その手牌はメンツ除去により可約である。
待ちでない牌列を既約とは扱わない。
-/
def waitCompletionCount (tiles : List Tile) : Nat :=
  (findWaitCompletions tiles).length

instance decidableIsTenpai (tiles : List Tile) : Decidable (IsTenpai tiles) := by
  rw [← waitingTiles_ne_nil_iff]
  infer_instance

/-- `tiles` から完成面子を1つ取り除いて得られる牌種リストの候補。 -/
def mentsuReductions (tiles : List Tile) : List (List Tile) :=
  meldChunkCandidates.filterMap fun mentsu =>
    removeTiles tiles mentsu.tiles

/-- 完成面子を1つ除いても同じ分解数の聴牌形が残るなら可約とする。 -/
def CanReduceMentsu (tiles : List Tile) : Prop :=
  1 < tiles.length ∧ IsTenpai tiles ∧
    (mentsuReductions tiles).any (fun remaining =>
      !(waitingTiles remaining).isEmpty &&
        waitCompletionCount remaining == waitCompletionCount tiles) = true

instance decidableCanReduceMentsu (tiles : List Tile) : Decidable (CanReduceMentsu tiles) := by
  unfold CanReduceMentsu
  infer_instance

/-- それ以上、完成面子除去で同じ待ち構造へ小さくできない聴牌形。 -/
def IsIrreducible (tiles : List Tile) (_ : IsTenpai tiles) : Prop :=
  ¬CanReduceMentsu tiles

instance decidableIsIrreducible (tiles : List Tile) (tenpai : IsTenpai tiles) :
    Decidable (IsIrreducible tiles tenpai) := by
  unfold IsIrreducible
  infer_instance

/-- 1枚手牌は単騎として既約である。 -/
theorem singleton_irreducible (tile : Tile) (tenpai : IsTenpai [tile]) :
    IsIrreducible [tile] tenpai := by
  intro reducible
  simpa using reducible.1

/-- 可約なら既約ではない。 -/
theorem not_irreducible_of_canReduceMentsu (tiles : List Tile)
    (tenpai : IsTenpai tiles) (reducible : CanReduceMentsu tiles) :
    ¬IsIrreducible tiles tenpai := by
  exact fun irreducible => irreducible reducible

def manzu (ranks : List Rank) : List Tile :=
  Tile.numberedTiles .Manzu ranks

def souzu (ranks : List Rank) : List Tile :=
  Tile.numberedTiles .Souzu ranks

end WaitCompletionFinder
