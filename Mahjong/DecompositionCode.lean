import Mahjong.Basic
import Mahjong.Pattern
import Mahjong.DecompositionFinder

/-!
# 発見済みDecompositionの部品種別コード

`DecompositionFinder.find` が発見した `Decomposition` を入力とし、牌の位置を忘れて、
待ち牌を除いた各分割を部品種別の多重集合として扱う。
異なる部品種別に異なる素数を割り当て、その積を代表元とする。
-/
namespace DecompositionCode

open DecompositionFinder

/-- 待ち牌を除いた後に見える部品種別。 -/
inductive DecompositionComponent
| tanki
| toitsu
| ryanmen
| kanchan
| penchan
| shuntsu
| koutsu
deriving BEq, DecidableEq, Repr

namespace DecompositionComponent

/-- すべての部品種別。キーの基数を部品数から導くためにも使う。 -/
def all : List DecompositionComponent :=
  [.tanki, .toitsu, .ryanmen, .kanchan, .penchan, .shuntsu, .koutsu]

/-- 部品種別の数。 -/
def count : Nat := all.length

/-- 部品種別に割り当てる素数。積をとることで多重集合の代表コードにする。 -/
def prime : DecompositionComponent → Nat
  | .tanki => 2
  | .toitsu => 3
  | .ryanmen => 5
  | .kanchan => 7
  | .penchan => 11
  | .shuntsu => 13
  | .koutsu => 17

end DecompositionComponent

/-- 具体的な牌種列を保持した部品。 -/
structure ConcreteDecompositionComponent where
  kind : DecompositionComponent
  tiles : List Tile
deriving BEq, DecidableEq, Repr

/-- 1つの待ち牌に対する、具体牌つきの形抽出。 -/
structure ConcreteDecompositionExtraction where
  wait : Tile
  components : List ConcreteDecompositionComponent
deriving BEq, DecidableEq, Repr

/-- 牌の位置を忘れ、部品種別だけを残した形抽出。 -/
structure AbstractDecompositionExtraction where
  wait : Tile
  components : List DecompositionComponent
deriving BEq, DecidableEq, Repr

/-- 待ち牌ごとの抽象形コード。 -/
structure DecompositionCodeEntry where
  wait : Tile
  code : Nat
deriving BEq, DecidableEq, Repr

private def completeComponent (chunk : TileChunk) : ConcreteDecompositionComponent :=
  { kind := match chunk with
      | .inl _ => .toitsu
      | .inr (.shuntsu _) => .shuntsu
      | .inr (.koutsu _) => .koutsu
    tiles := chunk.tiles }

private def componentWithoutWait (wait : Tile) (chunk : TileChunk) :
    Option ConcreteDecompositionComponent :=
  let incompleteTiles := chunk.tiles.erase wait
  let result kind := some { kind, tiles := incompleteTiles }
  match chunk with
    | .inl (.toitsu tile) =>
      if tile == wait then result .tanki else none
    | .inr (.koutsu tile) =>
      if tile == wait then result .toitsu else none
    | .inr (.shuntsu (.shuntsu suit start)) =>
      match wait with
      | .honor _ => none
      | .numbered waitSuit rank =>
          if waitSuit != suit then none
          else if rank == ShuntsuStart.firstRank start then
            result (if ShuntsuStart.isLast start then .penchan else .ryanmen)
          else if rank == ShuntsuStart.middleRank start then
            result .kanchan
          else if rank == ShuntsuStart.lastRank start then
            result (if ShuntsuStart.isFirst start then .penchan else .ryanmen)
          else none

private def componentProduct (components : List DecompositionComponent) : Nat :=
  components.foldl (fun product component => product * component.prime) 1

private def keyDigitOffset : Nat := 1
private def tileKeyBase : Nat := Tile.count + keyDigitOffset
private def maxComponentTiles : Nat := mentsuTileCount
private def maxDecompositionComponents : Nat := standardHandMentsuCount + standardHandPairCount
private def componentTileKeyStride : Nat := tileKeyBase ^ maxComponentTiles
private def extractionComponentKeyStride : Nat := DecompositionComponent.count * componentTileKeyStride
private def extractionWaitKeyStride : Nat := extractionComponentKeyStride ^ maxDecompositionComponents
private def abstractComponentKeyBase : Nat := DecompositionComponent.count + keyDigitOffset
private def waitKeyStride : Nat := Tile.count

private def decompositionComponentKey (component : DecompositionComponent) : Nat :=
  DecompositionComponent.all.idxOf component

private def concreteComponentKey (component : ConcreteDecompositionComponent) : Nat :=
  decompositionComponentKey component.kind * componentTileKeyStride +
    component.tiles.foldl
      (fun key tile => key * tileKeyBase + tile.orderKey + keyDigitOffset) 0

private def canonicalizeDecompositionExtraction
    (components : List ConcreteDecompositionComponent) : List ConcreteDecompositionComponent :=
  components.mergeSort fun first second =>
    concreteComponentKey first ≤ concreteComponentKey second

private def concreteDecompositionExtractionKey (extraction : ConcreteDecompositionExtraction) : Nat :=
  extraction.wait.orderKey * extractionWaitKeyStride +
    extraction.components.foldl
      (fun key component => key * extractionComponentKeyStride + concreteComponentKey component) 0

private def abstractDecompositionExtractionKey (extraction : AbstractDecompositionExtraction) : Nat :=
  extraction.components.foldl
    (fun key component =>
      key * abstractComponentKeyBase + decompositionComponentKey component + keyDigitOffset) 0 *
      waitKeyStride +
    extraction.wait.orderKey

private def decompositionCodeEntryKey (entry : DecompositionCodeEntry) : Nat :=
  entry.code * waitKeyStride + entry.wait.orderKey

private def deduplicateAndSortBy {α : Type} [BEq α]
    (key : α → Nat) (values : List α) : List α :=
  values.eraseDups.mergeSort fun first second => key first ≤ key second

private def decompositionExtractions (decomposition : Decomposition) :
    List (List ConcreteDecompositionComponent) :=
  let rec selectCompletedChunk : List TileChunk → List (List ConcreteDecompositionComponent)
    | [] => []
    | chunk :: rest =>
        let later := (selectCompletedChunk rest).map fun extraction =>
          completeComponent chunk :: extraction
        match componentWithoutWait decomposition.wait chunk with
        | some incomplete =>
            (incomplete :: rest.map completeComponent) :: later
        | none => later
  selectCompletedChunk decomposition.chunks

/-- 発見済みの待ちと分割から、待ち牌ごとの具体的な分解抽出を列挙する。 -/
def concreteDecompositionExtractions
    (decompositions : List Decomposition) : List ConcreteDecompositionExtraction :=
  let entries := decompositions.flatMap fun decomposition =>
      (decompositionExtractions decomposition).map fun extraction =>
        { wait := decomposition.wait
          components := canonicalizeDecompositionExtraction extraction }
  deduplicateAndSortBy concreteDecompositionExtractionKey entries

/-- 発見済みDecompositionから牌位置を忘れ、部品種別だけの抽出へ変換する。 -/
def abstractDecompositionExtractions
    (decompositions : List Decomposition) : List AbstractDecompositionExtraction :=
  concreteDecompositionExtractions decompositions
    |>.map (fun extraction =>
      { wait := extraction.wait
        components := extraction.components.map (fun component => component.kind) })
    |> deduplicateAndSortBy abstractDecompositionExtractionKey

/-- 発見済みDecompositionを、待ち牌ごとの素数積コードへ変換する。 -/
def decompositionCodeEntries
    (decompositions : List Decomposition) : List DecompositionCodeEntry :=
  abstractDecompositionExtractions decompositions
    |>.map (fun extraction =>
      { wait := extraction.wait
        code := componentProduct extraction.components })
    |> deduplicateAndSortBy decompositionCodeEntryKey

/-- 発見済みDecompositionから計算した、待ち牌を残す抽象形コード。 -/
def abstractDecompositionCodeWithWait
    (decompositions : List Decomposition) : List (Nat × Tile) :=
  decompositionCodeEntries decompositions
    |>.map fun entry => (entry.code, entry.wait)

/-- 発見済みDecompositionから待ち牌を忘れ、抽象形コードだけを列挙する。 -/
def abstractDecompositionCode (decompositions : List Decomposition) : List Nat :=
  decompositionCodeEntries decompositions
    |>.map (fun entry => entry.code)
    |> deduplicateAndSortBy id

/-! ## 牌列から探索して符号化する便利関数 -/

def findConcreteDecompositionExtractions (tiles : List Tile) : List ConcreteDecompositionExtraction :=
  concreteDecompositionExtractions (DecompositionFinder.find tiles)

def findAbstractDecompositionExtractions (tiles : List Tile) : List AbstractDecompositionExtraction :=
  abstractDecompositionExtractions (DecompositionFinder.find tiles)

def findDecompositionCodeEntries (tiles : List Tile) : List DecompositionCodeEntry :=
  decompositionCodeEntries (DecompositionFinder.find tiles)

def findAbstractDecompositionCodeWithWait (tiles : List Tile) : List (Nat × Tile) :=
  abstractDecompositionCodeWithWait (DecompositionFinder.find tiles)

def findAbstractDecompositionCode (tiles : List Tile) : List Nat :=
  abstractDecompositionCode (DecompositionFinder.find tiles)

private def decompositionCodeTestHand2345678 : List Tile :=
  Tile.numberedTiles .Manzu [1, 2, 3, 4, 5, 6, 7]
private def decompositionCodeTestHand1167888 : List Tile :=
  Tile.numberedTiles .Manzu [0, 0, 5, 6, 7, 7, 7]
private def decompositionCodeTestHand1166678 : List Tile :=
  Tile.numberedTiles .Manzu [0, 0, 5, 5, 5, 6, 7]

example : findAbstractDecompositionExtractions decompositionCodeTestHand2345678 =
  [{ wait := .numbered .Manzu 1, components := [.tanki, .shuntsu, .shuntsu] },
   { wait := .numbered .Manzu 4, components := [.tanki, .shuntsu, .shuntsu] },
   { wait := .numbered .Manzu 7, components := [.tanki, .shuntsu, .shuntsu] }] := by
  native_decide

example : findDecompositionCodeEntries decompositionCodeTestHand2345678 =
  [{ wait := .numbered .Manzu 1, code := 338 },
   { wait := .numbered .Manzu 4, code := 338 },
   { wait := .numbered .Manzu 7, code := 338 }] := by
  native_decide

example : findAbstractDecompositionCodeWithWait decompositionCodeTestHand2345678 =
  [(338, .numbered .Manzu 1),
   (338, .numbered .Manzu 4),
   (338, .numbered .Manzu 7)] := by native_decide
example : findAbstractDecompositionCode decompositionCodeTestHand2345678 = [338] := by native_decide
example : findAbstractDecompositionCode decompositionCodeTestHand1167888 = [117, 255] := by native_decide
example : findAbstractDecompositionCode decompositionCodeTestHand1166678 = [117, 255] := by native_decide
example : findAbstractDecompositionCode decompositionCodeTestHand1167888 =
  findAbstractDecompositionCode decompositionCodeTestHand1166678 := by
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

private def insertAbstractDecompositionClass (entry : String × List Nat) :
  List (List Nat × List String) → List (List Nat × List String)
  | [] => [(entry.2, [entry.1])]
  | current :: rest =>
      if current.1 == entry.2 then
        (current.1, current.2 ++ [entry.1]) :: rest
      else
        current :: insertAbstractDecompositionClass entry rest

def irreducibleSevenTileAbstractDecompositionClasses : List (List Nat × List String) :=
  irreducibleSingleSuitSevenTileExamples.foldl (fun classes entry =>
    insertAbstractDecompositionClass (entry.1, findAbstractDecompositionCode entry.2) classes) []

example : irreducibleSevenTileAbstractDecompositionClasses.length = 26 := by native_decide

example : irreducibleSevenTileAbstractDecompositionClasses.find? (fun entry =>
    entry.1 == [117, 255]) = some
      ([117, 255],
       ["1178999m", "1167888m", "1166678m", "1156777m", "1155567m",
        "1145666m", "1144456m", "1134555m", "1133345m", "1122234m",
        "1112399m", "1112388m", "1112377m", "1112366m", "1112355m"]) := by
  native_decide

end DecompositionCode
