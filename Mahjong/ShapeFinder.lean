import Mahjong.Shape
import Mathlib.Tactic

/-!
# 待ちと和了分割の探索

`IsStandardAgari`、`IsWaitFor`、`IsTenpai` が通常形の意味論を定め、
`Wait tiles` が聴牌牌列 `tiles` に結び付いた待ちの証拠を表す。
`waitingTiles` は実際の待ち牌を計算する決定手続きであり、`find` は、
待ち牌を加えた和了形をチャンクへ分解して得られる集合に対して正規化を行う。

このモジュールは物理牌ではなく、牌種 `Tile` のリストを対象にする。重複はリスト内の
出現回数で表し、`waitingTiles` では同じ牌種が5枚以上にならないよう `count < 4` を確認する。
-/
namespace ShapeFinder

/-- 通常形で順子を作れる3種類の数牌スート。 -/
def suits : List Suit := [.Manzu, .Pinzu, .Souzu]

/-- すべての字牌。 -/
def honors : List Honor :=
  [.East, .South, .West, .North, .White, .Green, .Red]

/-- 27種類すべての数牌。 -/
def numberedTiles : List Tile :=
  suits.flatMap fun suit => List.ofFn fun rank : Fin 9 =>
    Tile.numbered suit rank

/-- 待ち牌候補として使う34種類すべての牌種。 -/
def allTiles : List Tile :=
  numberedTiles ++ honors.map .honor

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
  allTiles.map .pair

/-- 完成面子候補。全順子候補と全刻子候補を含む。 -/
def meldChunkCandidates : List TileChunk :=
  (suits.flatMap fun suit =>
    List.ofFn fun start : Fin 7 =>
      TileChunk.shuntsu suit start) ++
  allTiles.map .koutsu

/-- 牌種リストを完成面子だけに分解する。`fuel` は残り面子数の上限として使う。 -/
def decomposeMelds : Nat → List Tile → List (List TileChunk)
  | 0, tiles =>
      if tiles.isEmpty then [[]] else []
  | fuel + 1, tiles =>
      List.flatten (meldChunkCandidates.map fun meld =>
        match removeTiles tiles meld.tiles with
        | some remaining =>
            (decomposeMelds fuel remaining).map fun chunks => meld :: chunks
        | none => [])

/-- 牌種リストを雀頭1つと完成面子列に分解する。 -/
def winningDecompositions (tiles : List Tile) : List (List TileChunk) :=
  List.flatten (pairChunkCandidates.map fun pairChunk =>
    match removeTiles tiles pairChunk.tiles with
    | some remaining =>
        (decomposeMelds (remaining.length / 3) remaining).map fun chunks =>
          pairChunk :: chunks
    | none => [])

/-- 牌種リストが通常形の和了形として分解できるか。 -/
def isWinning (tiles : List Tile) : Bool :=
  !(winningDecompositions tiles).isEmpty

/-- 牌種列が通常形（雀頭1つと完成面子列）の和了形であること。 -/
def IsStandardAgari (tiles : List Tile) : Prop :=
  isWinning tiles = true

/-- `candidate` を1枚加えると通常形で和了し、5枚目にもならないこと。 -/
def IsWaitFor (tiles : List Tile) (candidate : Tile) : Prop :=
  tiles.count candidate < 4 ∧ IsStandardAgari (candidate :: tiles)

/-- 牌種列が少なくとも1種類の通常形待ちを持つこと。 -/
def IsTenpai (tiles : List Tile) : Prop :=
  ∃ candidate, IsWaitFor tiles candidate

/-- 手牌に結び付いた通常形待ちの証拠。 -/
structure Wait (tiles : List Tile) where
  tile : Tile
  valid : IsWaitFor tiles tile

/-- 与えられた聴牌形に対し、加えると通常形で和了になる牌種を列挙する。 -/
def waitingTiles (tiles : List Tile) : List Tile :=
  allTiles.filter fun candidate =>
    (tiles.count candidate < 4) && isWinning (candidate :: tiles)

/-- すべての牌種は34種類の候補列に含まれる。 -/
theorem mem_allTiles (candidate : Tile) : candidate ∈ allTiles := by
  cases candidate with
  | numbered suit rank =>
      cases suit <;> fin_cases rank <;>
        simp [allTiles, numberedTiles, suits]
  | honor honor =>
      cases honor <;> simp [allTiles, honors]

/-- `waitingTiles` は `IsWaitFor` をちょうど判定する。 -/
theorem mem_waitingTiles_iff (tiles : List Tile) (candidate : Tile) :
    candidate ∈ waitingTiles tiles ↔ IsWaitFor tiles candidate := by
  simp [waitingTiles, mem_allTiles, IsWaitFor, IsStandardAgari,
    Bool.and_eq_true]

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
def find (tiles : List Tile) : List Shape :=
  ((waitingTiles tiles).flatMap fun wait =>
    (winningDecompositions (wait :: tiles)).map fun chunks =>
      { wait, chunks := TileChunk.canonicalize chunks }).eraseDups

/-!
## 分解に関する既約性

`decompositionCount` は待ち牌と和了形の組を数える。メンツを1つ除いた
聴牌形が同じ個数の分解を持つなら、その手牌はメンツ除去により可約である。
待ちでない牌列を既約とは扱わない。
-/
def decompositionCount (tiles : List Tile) : Nat :=
  (find tiles).length

/-- 従来名。新しいコードでは意味論を直接表す `IsTenpai` を使う。 -/
abbrev IsTenpaiTiles := IsTenpai

instance decidableIsTenpaiTiles (tiles : List Tile) : Decidable (IsTenpaiTiles tiles) := by
  change Decidable (IsTenpai tiles)
  rw [← waitingTiles_ne_nil_iff]
  infer_instance

/-- `tiles` から完成面子を1つ取り除いて得られる牌種リストの候補。 -/
def mentsuReductions (tiles : List Tile) : List (List Tile) :=
  meldChunkCandidates.filterMap fun mentsu =>
    removeTiles tiles mentsu.tiles

/-- 完成面子を1つ除いても同じ分解数の聴牌形が残るなら可約とする。 -/
def CanReduceMentsu (tiles : List Tile) : Prop :=
  1 < tiles.length ∧ IsTenpaiTiles tiles ∧
    (mentsuReductions tiles).any (fun remaining =>
      !(waitingTiles remaining).isEmpty &&
        decompositionCount remaining == decompositionCount tiles) = true

instance decidableCanReduceMentsu (tiles : List Tile) : Decidable (CanReduceMentsu tiles) := by
  unfold CanReduceMentsu
  infer_instance

/-- それ以上、完成面子除去で同じ待ち構造へ小さくできない聴牌形。 -/
def IsIrreducible (tiles : List Tile) : Prop :=
  tiles.length = 1 ∨
    (IsTenpaiTiles tiles ∧ ¬CanReduceMentsu tiles)

instance decidableIsIrreducible (tiles : List Tile) : Decidable (IsIrreducible tiles) := by
  unfold IsIrreducible
  infer_instance

/-- 1枚手牌は単騎として既約である。 -/
theorem singleton_irreducible (tile : Tile) : IsIrreducible [tile] := by
  simp [IsIrreducible]

/-- 可約なら既約ではない。 -/
theorem not_irreducible_of_canReduceMentsu (tiles : List Tile)
    (reducible : CanReduceMentsu tiles) : ¬IsIrreducible tiles := by
  rcases reducible with ⟨moreThanOne, tenpai, reduction⟩
  intro irreducible
  rcases irreducible with singleton | ⟨_, notReducible⟩
  · omega
  · exact notReducible ⟨moreThanOne, tenpai, reduction⟩

/-- スート名と絶対ランクを忘れた正規化後の牌。 -/
inductive NormalizedTile
| numbered (suitIndex rank : Nat)
| honor (honor : Honor)
deriving BEq, DecidableEq, Repr

/-- 正規化後の完成部品。 -/
inductive NormalizedChunk
| pair (tile : NormalizedTile)
| shuntsu (suitIndex start : Nat)
| koutsu (tile : NormalizedTile)
deriving BEq, DecidableEq, Repr

/-- 待ち牌と和了分解を平行移動で正規化したもの。 -/
structure NormalizedDecomposition where
  wait : NormalizedTile
  chunks : List NormalizedChunk
deriving BEq, DecidableEq, Repr

/-- 通常形待ち解析の結果。 -/
structure Analysis where
  decompositions : List NormalizedDecomposition
deriving BEq, DecidableEq, Repr

private def ranksIn (suit : Suit) (tiles : List Tile) : List Nat :=
  tiles.filterMap fun
    | .numbered tileSuit rank =>
        if tileSuit == suit then some rank.val else none
    | .honor _ => none

private def chunkTiles (decomposition : Shape) : List Tile :=
  decomposition.wait :: decomposition.chunks.flatMap TileChunk.tiles

private def suitHasTiles (tiles : List Tile) (suit : Suit) : Bool :=
  !(ranksIn suit tiles).isEmpty

private def presentSuits (tiles : List Tile) : List Suit :=
  suits.filter (suitHasTiles tiles)

private def suitIndexFrom : List Suit → Suit → Nat
  | [], _ => 0
  | current :: rest, suit =>
      if current == suit then 0 else suitIndexFrom rest suit + 1

private def lowestRank (tiles : List Tile) (suit : Suit) : Nat :=
  match ranksIn suit tiles with
  | [] => 0
  | first :: rest => rest.foldl Nat.min first

private def normalizeTile (tiles : List Tile) (present : List Suit) : Tile → NormalizedTile
  | .honor honor => .honor honor
  | .numbered suit rank =>
      .numbered (suitIndexFrom present suit) (rank.val - lowestRank tiles suit)

private def normalizeChunk (tiles : List Tile) (present : List Suit) : TileChunk → NormalizedChunk
  | .inl (.toitsu tile) => .pair (normalizeTile tiles present tile)
  | .inr (.shuntsu (.shuntsu suit start)) =>
      .shuntsu (suitIndexFrom present suit) (start.val - lowestRank tiles suit)
  | .inr (.koutsu tile) => .koutsu (normalizeTile tiles present tile)

/--
スート名とランクの平行移動を忘れて、同型な牌姿を同じ形として扱う。

各スート内の最小ランクを0へ移し、出現するスートを出現順に `0, 1, ...` と番号付けする。
-/
def normalizeByTranslation (decomposition : Shape) : NormalizedDecomposition :=
  let tiles := chunkTiles decomposition
  let present := presentSuits tiles
  { wait := normalizeTile tiles present decomposition.wait
    chunks := decomposition.chunks.map (normalizeChunk tiles present) }

/-- 任意の正規化関数で待ち分解集合を商としてまとめる。 -/
def analysisWith {α : Type} [DecidableEq α]
    (normalize : Shape → α) (tiles : List Tile) : List α :=
  (find tiles).map normalize |>.eraseDups

/-- 平行移動による正規化で通常形待ちを解析する。 -/
def analyzeWait (tiles : List Tile) : Analysis :=
  { decompositions := analysisWith normalizeByTranslation tiles }

private def manzu (ranks : List Rank) : List Tile :=
  ranks.map (.numbered .Manzu)

private def souzu (ranks : List Rank) : List Tile :=
  ranks.map (.numbered .Souzu)

-- Rank は 0 始まりなので、牌姿の数字から 1 を引いて記述する。
def testHandA : List Tile := manzu [2, 3, 4, 4, 4] ++ souzu [7, 7]
def testHandB : List Tile := manzu [1, 1, 2, 2, 3, 3, 4, 4, 5, 5]
def testHandC : List Tile := souzu [2, 2, 3, 3, 4, 4, 5, 5, 6, 6]
def testHandD : List Tile := manzu [1, 1, 2, 2, 3, 3, 4, 4] ++ souzu [6, 6]
def testHand3456678 : List Tile := manzu [2, 3, 4, 5, 5, 6, 7]
def testHand2345678 : List Tile := manzu [1, 2, 3, 4, 5, 6, 7]
def testHand3334556 : List Tile := manzu [2, 2, 2, 3, 4, 4, 5]
def testHand3335678 : List Tile := manzu [2, 2, 2, 4, 5, 6, 7]
def testHand3335567 : List Tile := manzu [2, 2, 2, 4, 4, 5, 6]
def testHand3335777 : List Tile := manzu [2, 2, 2, 4, 6, 6, 6]
def testHand1167888 : List Tile := manzu [0, 0, 5, 6, 7, 7, 7]
def testHand1166678 : List Tile := manzu [0, 0, 5, 5, 5, 6, 7]

private def manzuPair (rank : Rank) : TileChunk :=
  .pair (.numbered .Manzu rank)

private def manzuShuntsu (start : Fin 7) : TileChunk :=
  .shuntsu .Manzu start

private def manzuKoutsu (rank : Rank) : TileChunk :=
  .koutsu (.numbered .Manzu rank)

private def manzuDecomposition (wait : Rank) (chunks : List TileChunk) : Shape :=
  { wait := .numbered .Manzu wait, chunks }

example : waitingTiles testHandA =
  manzu [1, 4] ++ souzu [7] := by native_decide

example : waitingTiles testHandB = manzu [1, 2, 4, 5] := by native_decide

example : waitingTiles testHandC = souzu [2, 3, 5, 6] := by native_decide

example : waitingTiles testHandD = manzu [1, 4] ++ souzu [6] := by native_decide

example : analyzeWait testHandB = analyzeWait testHandC := by native_decide
example : analyzeWait testHandB ≠ analyzeWait testHandD := by native_decide
example : analyzeWait testHandC ≠ analyzeWait testHandD := by native_decide

-- 3456678: 単騎 3・6、両面 6・9
example : find testHand3456678 =
  [manzuDecomposition 2 [manzuPair 2, manzuShuntsu 3, manzuShuntsu 5],
   manzuDecomposition 5 [manzuPair 5, manzuShuntsu 2, manzuShuntsu 5],
   manzuDecomposition 8 [manzuPair 5, manzuShuntsu 2, manzuShuntsu 6]] ∧
  (find testHand3456678).length = 3 := by native_decide

-- 2345678: 単騎 2・5・8
example : find testHand2345678 =
  [manzuDecomposition 1 [manzuPair 1, manzuShuntsu 2, manzuShuntsu 5],
   manzuDecomposition 4 [manzuPair 4, manzuShuntsu 1, manzuShuntsu 5],
   manzuDecomposition 7 [manzuPair 7, manzuShuntsu 1, manzuShuntsu 4]] ∧
  (find testHand2345678).length = 3 := by native_decide

-- 3334556: 単騎 5、嵌張 5、両面 4・7
example : find testHand3334556 =
  [manzuDecomposition 3 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 3],
   manzuDecomposition 4 [manzuPair 4, manzuShuntsu 3, manzuKoutsu 2],
   manzuDecomposition 6 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 4]] ∧
  (find testHand3334556).length = 3 := by native_decide

-- 3335678: 単騎 5・8、嵌張 4
example : find testHand3335678 =
  [manzuDecomposition 3 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 5],
   manzuDecomposition 4 [manzuPair 4, manzuShuntsu 5, manzuKoutsu 2],
   manzuDecomposition 7 [manzuPair 7, manzuShuntsu 4, manzuKoutsu 2]] ∧
  (find testHand3335678).length = 3 := by native_decide

-- 3335567: 単騎 5、嵌張 4、両面 5・8
example : find testHand3335567 =
  [manzuDecomposition 3 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 4],
   manzuDecomposition 4 [manzuPair 4, manzuShuntsu 4, manzuKoutsu 2],
   manzuDecomposition 7 [manzuPair 4, manzuShuntsu 5, manzuKoutsu 2]] ∧
  (find testHand3335567).length = 3 := by native_decide

-- 3335777: 単騎 5、嵌張 4・6
example : find testHand3335777 =
  [manzuDecomposition 3 [manzuPair 2, manzuShuntsu 2, manzuKoutsu 6],
   manzuDecomposition 4 [manzuPair 4, manzuKoutsu 2, manzuKoutsu 6],
   manzuDecomposition 5 [manzuPair 6, manzuShuntsu 4, manzuKoutsu 2]] ∧
  (find testHand3335777).length = 3 := by native_decide

end ShapeFinder
