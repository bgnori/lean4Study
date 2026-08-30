import Mahjong.Pattern

/-!
## 通常形の待ち分析

`waitingTiles` は実際の待ち牌を返す。`analyzeWait` は、待ち牌を加えた
和了形をチャンクへ分解して得られる集合に対して正規化を行う。
-/
namespace StandardWait

def suits : List Suit := [.Manzu, .Pinzu, .Souzu]

def honors : List Honor :=
  [.East, .South, .West, .North, .White, .Green, .Red]

def numberedTiles : List Tile :=
  suits.flatMap fun suit => List.ofFn fun rank : Fin 9 =>
    Tile.numbered suit rank

def allTiles : List Tile :=
  numberedTiles ++ honors.map .honor

def removeTiles : List Tile → List Tile → Option (List Tile)
  | available, [] => some available
  | available, wanted :: rest =>
      if available.contains wanted then
        removeTiles (available.erase wanted) rest
      else
        none

inductive TileChunk
| pair (tile : Tile)
| shuntsu (suit : Suit) (start : Fin 7)
| koutsu (tile : Tile)
deriving BEq, DecidableEq, Repr

namespace TileChunk

def tiles : TileChunk → List Tile
  | .pair tile => pairTiles tile
  | .shuntsu suit start => numberedRun suit start
  | .koutsu tile => koutsuTiles tile

private def suitKey : Suit → Nat
  | .Manzu => 0
  | .Pinzu => 1
  | .Souzu => 2

private def honorKey : Honor → Nat
  | .East => 0
  | .South => 1
  | .West => 2
  | .North => 3
  | .White => 4
  | .Green => 5
  | .Red => 6

private def tileKey : Tile → Nat
  | .numbered suit rank => suitKey suit * 9 + rank.val
  | .honor honor => 27 + honorKey honor

private def orderKey : TileChunk → Nat
  | .pair tile => tileKey tile
  | .shuntsu suit start => 34 + suitKey suit * 7 + start.val
  | .koutsu tile => 55 + tileKey tile

def canonicalize (chunks : List TileChunk) : List TileChunk :=
  chunks.mergeSort fun first second => orderKey first ≤ orderKey second

end TileChunk

structure WaitDecomposition where
  wait : Tile
  chunks : List TileChunk
deriving BEq, DecidableEq, Repr

def pairChunkCandidates : List TileChunk :=
  allTiles.map .pair

def meldChunkCandidates : List TileChunk :=
  (suits.flatMap fun suit =>
    List.ofFn fun start : Fin 7 =>
      TileChunk.shuntsu suit start) ++
  allTiles.map .koutsu

def decomposeMelds : Nat → List Tile → List (List TileChunk)
  | 0, tiles =>
      if tiles.isEmpty then [[]] else []
  | fuel + 1, tiles =>
      List.flatten (meldChunkCandidates.map fun meld =>
        match removeTiles tiles meld.tiles with
        | some remaining =>
            (decomposeMelds fuel remaining).map fun chunks => meld :: chunks
        | none => [])

def winningDecompositions (tiles : List Tile) : List (List TileChunk) :=
  List.flatten (pairChunkCandidates.map fun pairChunk =>
    match removeTiles tiles pairChunk.tiles with
    | some remaining =>
        (decomposeMelds (remaining.length / 3) remaining).map fun chunks =>
          pairChunk :: chunks
    | none => [])

def isWinning (tiles : List Tile) : Bool :=
  !(winningDecompositions tiles).isEmpty

def waitingTiles (tiles : List Tile) : List Tile :=
  allTiles.filter fun candidate =>
    (tiles.count candidate < 4) && isWinning (candidate :: tiles)

def waitDecompositionSet (tiles : List Tile) : List WaitDecomposition :=
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
  (waitDecompositionSet tiles).length

def IsTenpaiTiles (tiles : List Tile) : Prop :=
  waitingTiles tiles ≠ []

instance decidableIsTenpaiTiles (tiles : List Tile) : Decidable (IsTenpaiTiles tiles) := by
  unfold IsTenpaiTiles
  infer_instance

def mentsuReductions (tiles : List Tile) : List (List Tile) :=
  meldChunkCandidates.filterMap fun mentsu =>
    removeTiles tiles mentsu.tiles

def CanReduceMentsu (tiles : List Tile) : Prop :=
  1 < tiles.length ∧ IsTenpaiTiles tiles ∧
    (mentsuReductions tiles).any (fun remaining =>
      !(waitingTiles remaining).isEmpty &&
        decompositionCount remaining == decompositionCount tiles) = true

instance decidableCanReduceMentsu (tiles : List Tile) : Decidable (CanReduceMentsu tiles) := by
  unfold CanReduceMentsu
  infer_instance

def IsIrreducible (tiles : List Tile) : Prop :=
  tiles.length = 1 ∨
    (IsTenpaiTiles tiles ∧ ¬CanReduceMentsu tiles)

instance decidableIsIrreducible (tiles : List Tile) : Decidable (IsIrreducible tiles) := by
  unfold IsIrreducible
  infer_instance

theorem singleton_irreducible (tile : Tile) : IsIrreducible [tile] := by
  simp [IsIrreducible]

theorem not_irreducible_of_canReduceMentsu (tiles : List Tile)
    (reducible : CanReduceMentsu tiles) : ¬IsIrreducible tiles := by
  rcases reducible with ⟨moreThanOne, tenpai, reduction⟩
  intro irreducible
  rcases irreducible with singleton | ⟨_, notReducible⟩
  · omega
  · exact notReducible ⟨moreThanOne, tenpai, reduction⟩

inductive NormalizedTile
| numbered (suitIndex rank : Nat)
| honor (honor : Honor)
deriving BEq, DecidableEq, Repr

inductive NormalizedChunk
| pair (tile : NormalizedTile)
| shuntsu (suitIndex start : Nat)
| koutsu (tile : NormalizedTile)
deriving BEq, DecidableEq, Repr

structure NormalizedDecomposition where
  wait : NormalizedTile
  chunks : List NormalizedChunk
deriving BEq, DecidableEq, Repr

structure Analysis where
  decompositions : List NormalizedDecomposition
deriving BEq, DecidableEq, Repr

private def ranksIn (suit : Suit) (tiles : List Tile) : List Nat :=
  tiles.filterMap fun
    | .numbered tileSuit rank =>
        if tileSuit == suit then some rank.val else none
    | .honor _ => none

private def chunkTiles (decomposition : WaitDecomposition) : List Tile :=
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
  | .pair tile => .pair (normalizeTile tiles present tile)
  | .shuntsu suit start =>
      .shuntsu (suitIndexFrom present suit) (start.val - lowestRank tiles suit)
  | .koutsu tile => .koutsu (normalizeTile tiles present tile)

def normalizeByTranslation (decomposition : WaitDecomposition) : NormalizedDecomposition :=
  let tiles := chunkTiles decomposition
  let present := presentSuits tiles
  { wait := normalizeTile tiles present decomposition.wait
    chunks := decomposition.chunks.map (normalizeChunk tiles present) }

def analysisWith {α : Type} [DecidableEq α]
    (normalize : WaitDecomposition → α) (tiles : List Tile) : List α :=
  (waitDecompositionSet tiles).map normalize |>.eraseDups

def analyzeWait (tiles : List Tile) : Analysis :=
  { decompositions := analysisWith normalizeByTranslation tiles }

/-!
## 部品種別による商

牌の位置を忘れ、待ち牌を除いた各分解を部品種別の多重集合として扱う。
異なる部品種別に異なる素数を割り当て、その積を代表元とする。
-/
inductive ShapeComponent
| tanki
| toitsu
| ryanmen
| kanchan
| penchan
| shuntsu
| koutsu
deriving BEq, DecidableEq, Repr

namespace ShapeComponent

def prime : ShapeComponent → Nat
  | .tanki => 2
  | .toitsu => 3
  | .ryanmen => 5
  | .kanchan => 7
  | .penchan => 11
  | .shuntsu => 13
  | .koutsu => 17

end ShapeComponent

structure ConcreteShapeComponent where
  kind : ShapeComponent
  tiles : List Tile
deriving BEq, DecidableEq, Repr

structure ConcreteShapeExtraction where
  wait : Tile
  components : List ConcreteShapeComponent
deriving BEq, DecidableEq, Repr

structure AbstractShapeExtraction where
  wait : Tile
  components : List ShapeComponent
deriving BEq, DecidableEq, Repr

structure ShapeCodeEntry where
  wait : Tile
  code : Nat
deriving BEq, DecidableEq, Repr

private def completeComponent (chunk : TileChunk) : ConcreteShapeComponent :=
  { kind := match chunk with
      | .pair _ => .toitsu
      | .shuntsu .. => .shuntsu
      | .koutsu _ => .koutsu
    tiles := chunk.tiles }

private def componentWithoutWait (wait : Tile) (chunk : TileChunk) :
    Option ConcreteShapeComponent :=
  let incompleteTiles := chunk.tiles.erase wait
  let result kind := some { kind, tiles := incompleteTiles }
  match chunk with
  | .pair tile =>
      if tile == wait then result .tanki else none
  | .koutsu tile =>
      if tile == wait then result .toitsu else none
  | .shuntsu suit start =>
      match wait with
      | .honor _ => none
      | .numbered waitSuit rank =>
          if waitSuit != suit then none
          else if rank.val == start.val then
            result (if start.val == 6 then .penchan else .ryanmen)
          else if rank.val == start.val + 1 then
            result .kanchan
          else if rank.val == start.val + 2 then
            result (if start.val == 0 then .penchan else .ryanmen)
          else none

private def componentProduct (components : List ShapeComponent) : Nat :=
  components.foldl (fun product component => product * component.prime) 1

private def shapeComponentKey : ShapeComponent → Nat
  | .tanki => 0
  | .toitsu => 1
  | .ryanmen => 2
  | .kanchan => 3
  | .penchan => 4
  | .shuntsu => 5
  | .koutsu => 6

private def concreteTileKey : Tile → Nat
  | .numbered suit rank =>
      (match suit with | .Manzu => 0 | .Pinzu => 1 | .Souzu => 2) * 9 + rank.val
  | .honor honor => 27 + match honor with
      | .East => 0 | .South => 1 | .West => 2 | .North => 3
      | .White => 4 | .Green => 5 | .Red => 6

private def concreteComponentKey (component : ConcreteShapeComponent) : Nat :=
  shapeComponentKey component.kind * 50000 +
    component.tiles.foldl (fun key tile => key * 35 + concreteTileKey tile + 1) 0

private def canonicalizeShapeExtraction
    (components : List ConcreteShapeComponent) : List ConcreteShapeComponent :=
  components.mergeSort fun first second =>
    concreteComponentKey first ≤ concreteComponentKey second

private def concreteShapeExtractionKey (extraction : ConcreteShapeExtraction) : Nat :=
  concreteTileKey extraction.wait * 100000000 +
    extraction.components.foldl (fun key component => key * 500000 + concreteComponentKey component) 0

private def abstractShapeExtractionKey (extraction : AbstractShapeExtraction) : Nat :=
  extraction.components.foldl (fun key component => key * 10 + shapeComponentKey component + 1) 0 * 100 +
    concreteTileKey extraction.wait

private def shapeCodeEntryKey (entry : ShapeCodeEntry) : Nat :=
  entry.code * 100 + concreteTileKey entry.wait

private def decompositionShapeExtractions (decomposition : WaitDecomposition) :
    List (List ConcreteShapeComponent) :=
  let rec selectCompletedChunk : List TileChunk → List (List ConcreteShapeComponent)
    | [] => []
    | chunk :: rest =>
        let later := (selectCompletedChunk rest).map fun extraction =>
          completeComponent chunk :: extraction
        match componentWithoutWait decomposition.wait chunk with
        | some incomplete =>
            (incomplete :: rest.map completeComponent) :: later
        | none => later
  selectCompletedChunk decomposition.chunks

def concreteShapeExtractions (tiles : List Tile) : List ConcreteShapeExtraction :=
  let entries := (waitDecompositionSet tiles).flatMap fun decomposition =>
      (decompositionShapeExtractions decomposition).map fun extraction =>
        { wait := decomposition.wait
          components := canonicalizeShapeExtraction extraction }
  entries
    |>.eraseDups
    |>.mergeSort fun first second =>
      concreteShapeExtractionKey first ≤ concreteShapeExtractionKey second

def abstractShapeExtractions (tiles : List Tile) : List AbstractShapeExtraction :=
  concreteShapeExtractions tiles
    |>.map (fun extraction =>
      { wait := extraction.wait
        components := extraction.components.map (fun component => component.kind) })
    |>.eraseDups
    |>.mergeSort fun first second =>
      abstractShapeExtractionKey first ≤ abstractShapeExtractionKey second

def shapeCodeEntries (tiles : List Tile) : List ShapeCodeEntry :=
  abstractShapeExtractions tiles
    |>.map (fun extraction =>
      { wait := extraction.wait
        code := componentProduct extraction.components })
    |>.eraseDups
    |>.mergeSort fun first second =>
      shapeCodeEntryKey first ≤ shapeCodeEntryKey second

def abstractShapeCodeWithWait (tiles : List Tile) : List (Nat × Tile) :=
  shapeCodeEntries tiles
    |>.map fun entry => (entry.code, entry.wait)

def abstractShapeCode (tiles : List Tile) : List Nat :=
  shapeCodeEntries tiles
    |>.map (fun entry => entry.code)
    |>.eraseDups
    |>.mergeSort (· ≤ ·)

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

example : abstractShapeExtractions testHand2345678 =
  [{ wait := .numbered .Manzu 1, components := [.tanki, .shuntsu, .shuntsu] },
   { wait := .numbered .Manzu 4, components := [.tanki, .shuntsu, .shuntsu] },
   { wait := .numbered .Manzu 7, components := [.tanki, .shuntsu, .shuntsu] }] := by
  native_decide

example : shapeCodeEntries testHand2345678 =
  [{ wait := .numbered .Manzu 1, code := 338 },
   { wait := .numbered .Manzu 4, code := 338 },
   { wait := .numbered .Manzu 7, code := 338 }] := by
  native_decide

example : abstractShapeCodeWithWait testHand2345678 =
  [(338, .numbered .Manzu 1),
   (338, .numbered .Manzu 4),
   (338, .numbered .Manzu 7)] := by native_decide
example : abstractShapeCode testHand2345678 = [338] := by native_decide
example : abstractShapeCode testHand1167888 = [117, 255] := by native_decide
example : abstractShapeCode testHand1166678 = [117, 255] := by native_decide
example : abstractShapeCode testHand1167888 = abstractShapeCode testHand1166678 := by
  native_decide

/--
The 53 irreducible seven-tile waits using one numbered suit, normalized so the
lowest rank is 1.  Replacing `m` with `p` or `s`, or translating a pattern
without leaving ranks 1--9, gives equivalent concrete examples.
-/
def irreducibleSingleSuitSevenTileExamples : List (String × List Tile) :=
  [("1345666m", manzu [0, 2, 3, 4, 5, 5, 5]),
   ("1234666m", manzu [0, 1, 2, 3, 5, 5, 5]),
   ("1234567m", manzu [0, 1, 2, 3, 4, 5, 6]),
   ("1234555m", manzu [0, 1, 2, 3, 4, 4, 4]),
   ("1234456m", manzu [0, 1, 2, 3, 3, 4, 5]),
   ("1233334m", manzu [0, 1, 2, 2, 2, 2, 3]),
   ("1223344m", manzu [0, 1, 1, 2, 2, 3, 3]),
   ("1222345m", manzu [0, 1, 1, 1, 2, 3, 4]),
   ("1222333m", manzu [0, 1, 1, 1, 2, 2, 2]),
   ("1222234m", manzu [0, 1, 1, 1, 1, 2, 3]),
   ("1178999m", manzu [0, 0, 6, 7, 8, 8, 8]),
   ("1167888m", manzu [0, 0, 5, 6, 7, 7, 7]),
   ("1166678m", manzu [0, 0, 5, 5, 5, 6, 7]),
   ("1156777m", manzu [0, 0, 4, 5, 6, 6, 6]),
   ("1155567m", manzu [0, 0, 4, 4, 4, 5, 6]),
   ("1145678m", manzu [0, 0, 3, 4, 5, 6, 7]),
   ("1145666m", manzu [0, 0, 3, 4, 5, 5, 5]),
   ("1144456m", manzu [0, 0, 3, 3, 3, 4, 5]),
   ("1134567m", manzu [0, 0, 2, 3, 4, 5, 6]),
   ("1134555m", manzu [0, 0, 2, 3, 4, 4, 4]),
   ("1133345m", manzu [0, 0, 2, 2, 2, 3, 4]),
   ("1123456m", manzu [0, 0, 1, 2, 3, 4, 5]),
   ("1123444m", manzu [0, 0, 1, 2, 3, 3, 3]),
   ("1123344m", manzu [0, 0, 1, 2, 2, 3, 3]),
   ("1123333m", manzu [0, 0, 1, 2, 2, 2, 2]),
   ("1122344m", manzu [0, 0, 1, 1, 2, 3, 3]),
   ("1122334m", manzu [0, 0, 1, 1, 2, 2, 3]),
   ("1122333m", manzu [0, 0, 1, 1, 2, 2, 2]),
   ("1122234m", manzu [0, 0, 1, 1, 1, 2, 3]),
   ("1122233m", manzu [0, 0, 1, 1, 1, 2, 2]),
   ("1122223m", manzu [0, 0, 1, 1, 1, 1, 2]),
   ("1113555m", manzu [0, 0, 0, 2, 4, 4, 4]),
   ("1113456m", manzu [0, 0, 0, 2, 3, 4, 5]),
   ("1113444m", manzu [0, 0, 0, 2, 3, 3, 3]),
   ("1113345m", manzu [0, 0, 0, 2, 2, 3, 4]),
   ("1113333m", manzu [0, 0, 0, 2, 2, 2, 2]),
   ("1112444m", manzu [0, 0, 0, 1, 3, 3, 3]),
   ("1112399m", manzu [0, 0, 0, 1, 2, 8, 8]),
   ("1112388m", manzu [0, 0, 0, 1, 2, 7, 7]),
   ("1112377m", manzu [0, 0, 0, 1, 2, 6, 6]),
   ("1112366m", manzu [0, 0, 0, 1, 2, 5, 5]),
   ("1112355m", manzu [0, 0, 0, 1, 2, 4, 4]),
   ("1112346m", manzu [0, 0, 0, 1, 2, 3, 5]),
   ("1112345m", manzu [0, 0, 0, 1, 2, 3, 4]),
   ("1112344m", manzu [0, 0, 0, 1, 2, 3, 3]),
   ("1112334m", manzu [0, 0, 0, 1, 2, 2, 3]),
   ("1112333m", manzu [0, 0, 0, 1, 2, 2, 2]),
   ("1112234m", manzu [0, 0, 0, 1, 1, 2, 3]),
   ("1112233m", manzu [0, 0, 0, 1, 1, 2, 2]),
   ("1112223m", manzu [0, 0, 0, 1, 1, 1, 2]),
   ("1112222m", manzu [0, 0, 0, 1, 1, 1, 1]),
   ("1111333m", manzu [0, 0, 0, 0, 2, 2, 2]),
   ("1111222m", manzu [0, 0, 0, 0, 1, 1, 1])]

example : irreducibleSingleSuitSevenTileExamples.length = 53 := by native_decide

example : irreducibleSingleSuitSevenTileExamples.all
    (fun entry => decide (IsIrreducible entry.2)) = true := by
  native_decide

private def insertAbstractShapeClass (entry : String × List Nat) :
  List (List Nat × List String) → List (List Nat × List String)
  | [] => [(entry.2, [entry.1])]
  | current :: rest =>
      if current.1 == entry.2 then
        (current.1, current.2 ++ [entry.1]) :: rest
      else
        current :: insertAbstractShapeClass entry rest

def irreducibleSevenTileAbstractShapeClasses : List (List Nat × List String) :=
  irreducibleSingleSuitSevenTileExamples.foldl (fun classes entry =>
    insertAbstractShapeClass (entry.1, abstractShapeCode entry.2) classes) []

example : irreducibleSevenTileAbstractShapeClasses.length = 26 := by native_decide

example : irreducibleSevenTileAbstractShapeClasses.find? (fun entry =>
    entry.1 == [117, 255]) = some
      ([117, 255],
       ["1178999m", "1167888m", "1166678m", "1156777m", "1155567m",
        "1145666m", "1144456m", "1134555m", "1133345m", "1122234m",
        "1112399m", "1112388m", "1112377m", "1112366m", "1112355m"]) := by
  native_decide

private def manzuPair (rank : Rank) : TileChunk :=
  .pair (.numbered .Manzu rank)

private def manzuShuntsu (start : Fin 7) : TileChunk :=
  .shuntsu .Manzu start

private def manzuKoutsu (rank : Rank) : TileChunk :=
  .koutsu (.numbered .Manzu rank)

private def manzuDecomposition (wait : Rank) (chunks : List TileChunk) : WaitDecomposition :=
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
example : waitDecompositionSet testHand3456678 =
  [manzuDecomposition 2 [manzuPair 2, manzuShuntsu 3, manzuShuntsu 5],
   manzuDecomposition 5 [manzuPair 5, manzuShuntsu 2, manzuShuntsu 5],
   manzuDecomposition 8 [manzuPair 5, manzuShuntsu 2, manzuShuntsu 6]] ∧
  (waitDecompositionSet testHand3456678).length = 3 := by native_decide

-- 2345678: 単騎 2・5・8
example : waitDecompositionSet testHand2345678 =
  [manzuDecomposition 1 [manzuPair 1, manzuShuntsu 2, manzuShuntsu 5],
   manzuDecomposition 4 [manzuPair 4, manzuShuntsu 1, manzuShuntsu 5],
   manzuDecomposition 7 [manzuPair 7, manzuShuntsu 1, manzuShuntsu 4]] ∧
  (waitDecompositionSet testHand2345678).length = 3 := by native_decide

-- 3334556: 単騎 5、嵌張 5、両面 4・7
example : waitDecompositionSet testHand3334556 =
  [manzuDecomposition 3 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 3],
   manzuDecomposition 4 [manzuPair 4, manzuShuntsu 3, manzuKoutsu 2],
   manzuDecomposition 6 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 4]] ∧
  (waitDecompositionSet testHand3334556).length = 3 := by native_decide

-- 3335678: 単騎 5・8、嵌張 4
example : waitDecompositionSet testHand3335678 =
  [manzuDecomposition 3 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 5],
   manzuDecomposition 4 [manzuPair 4, manzuShuntsu 5, manzuKoutsu 2],
   manzuDecomposition 7 [manzuPair 7, manzuShuntsu 4, manzuKoutsu 2]] ∧
  (waitDecompositionSet testHand3335678).length = 3 := by native_decide

-- 3335567: 単騎 5、嵌張 4、両面 5・8
example : waitDecompositionSet testHand3335567 =
  [manzuDecomposition 3 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 4],
   manzuDecomposition 4 [manzuPair 4, manzuShuntsu 4, manzuKoutsu 2],
   manzuDecomposition 7 [manzuPair 4, manzuShuntsu 5, manzuKoutsu 2]] ∧
  (waitDecompositionSet testHand3335567).length = 3 := by native_decide

-- 3335777: 単騎 5、嵌張 4・6
example : waitDecompositionSet testHand3335777 =
  [manzuDecomposition 3 [manzuPair 2, manzuShuntsu 2, manzuKoutsu 6],
   manzuDecomposition 4 [manzuPair 4, manzuKoutsu 2, manzuKoutsu 6],
   manzuDecomposition 5 [manzuPair 6, manzuShuntsu 4, manzuKoutsu 2]] ∧
  (waitDecompositionSet testHand3335777).length = 3 := by native_decide

end StandardWait

