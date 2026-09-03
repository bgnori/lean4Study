import Mahjong.Basic
import Mahjong.Pattern
import Mahjong.WaitCompletionFinder

/-!
# 発見済みWaitCompletionのReadingコード

このモジュールでいう `Reading` は、麻雀一般の「相手の待ちを推測する待ち読み」ではない。
1つの待ち牌に対して、待ち牌を除いた和了分割の部品がどのような種別として見えるかを表す
観測結果である。

`WaitCompletionFinder.findWaitCompletions` が発見した `WaitCompletion` を入力とし、牌の位置を忘れて、
待ち牌を除いた各分割を部品種別の多重集合として扱う。
異なる部品種別に異なる素数を割り当て、その積を代表元とする。
-/
namespace WaitReadingCode

open WaitCompletionFinder

/-- 待ち牌を除いた後に見える部品種別。 -/
inductive WaitReadingComponentKind
| tanki
| toitsu
| ryanmen
| kanchan
| penchan
| shuntsu
| koutsu
deriving BEq, DecidableEq, Repr

namespace WaitReadingComponentKind

/-- すべての部品種別。キーの基数を部品数から導くためにも使う。 -/
def all : List WaitReadingComponentKind :=
  [.tanki, .toitsu, .ryanmen, .kanchan, .penchan, .shuntsu, .koutsu]

/-- 部品種別の数。 -/
def count : Nat := all.length

/-- 部品種別に割り当てる素数。積をとることで多重集合の代表コードにする。 -/
def prime : WaitReadingComponentKind → Nat
  | .tanki => 2
  | .toitsu => 3
  | .ryanmen => 5
  | .kanchan => 7
  | .penchan => 11
  | .shuntsu => 13
  | .koutsu => 17

end WaitReadingComponentKind

/-- 具体的な牌種列を保持した部品。 -/
structure ConcreteWaitReadingComponent where
  kind : WaitReadingComponentKind
  tiles : List Tile
deriving BEq, DecidableEq, Repr

/-- 1つの待ち牌に対する、具体牌付きのReading。 -/
structure ConcreteWaitReading where
  wait : Tile
  components : List ConcreteWaitReadingComponent
deriving BEq, DecidableEq, Repr

/-- 完成面子を除いた核成分列と、除去した面子を分けて保持するReading。 -/
structure IrreducibleWaitReading where
  wait : Tile
  core : List ConcreteWaitReadingComponent
  removedMentsu : List ConcreteWaitReadingComponent
deriving BEq, DecidableEq, Repr

/--
完成面子の文脈を忘れた、比較可能な待ち核。

待ち核は、1つの待ち牌と、完成面子を除いたあとに残る核成分列の組である。
`IrreducibleWaitReading.core` は具体牌付きの核成分列を保持し、`removedMentsu` はそこから分離された完成面子を保持する。
`WaitCore` は比較に必要な待ち牌と核成分列だけを残す。
-/
structure WaitCore where
  wait : Tile
  components : List ConcreteWaitReadingComponent
deriving BEq, DecidableEq, Repr

/-- 牌の位置を忘れ、部品種別だけを残したReading。 -/
structure AbstractWaitReading where
  wait : Tile
  components : List WaitReadingComponentKind
deriving BEq, DecidableEq, Repr

/-- 待ち牌ごとの抽象形コード。 -/
structure WaitReadingCodeEntry where
  wait : Tile
  code : Nat
deriving BEq, DecidableEq, Repr

private def completeComponent (chunk : TileChunk) : ConcreteWaitReadingComponent :=
  { kind := match chunk with
      | .inl _ => .toitsu
      | .inr (.shuntsu _) => .shuntsu
      | .inr (.koutsu _) => .koutsu
    tiles := chunk.tiles }

/-- 完成部品から指定した待ち牌を除いたときに生じる不完全部品の種別。 -/
def componentKindAfterRemovingWait (wait : Tile) (chunk : TileChunk) :
    Option WaitReadingComponentKind :=
  match chunk with
    | .inl (.toitsu tile) =>
      if tile == wait then some .tanki else none
    | .inr (.koutsu tile) =>
      if tile == wait then some .toitsu else none
    | .inr (.shuntsu (.shuntsu suit start)) =>
      match wait with
      | .honor _ => none
      | .numbered waitSuit rank =>
          if waitSuit != suit then none
          else if rank == ShuntsuStart.firstRank start then
            some (if ShuntsuStart.isLast start then .penchan else .ryanmen)
          else if rank == ShuntsuStart.middleRank start then
            some .kanchan
          else if rank == ShuntsuStart.lastRank start then
            some (if ShuntsuStart.isFirst start then .penchan else .ryanmen)
          else none

private def componentAfterRemovingWait (wait : Tile) (chunk : TileChunk) :
    Option ConcreteWaitReadingComponent :=
  (componentKindAfterRemovingWait wait chunk).map fun kind =>
    { kind, tiles := chunk.tiles.erase wait }

private def componentProduct (components : List WaitReadingComponentKind) : Nat :=
  components.foldl (fun product component => product * component.prime) 1

private def keyDigitOffset : Nat := 1
private def tileKeyBase : Nat := Tile.count + keyDigitOffset
private def maxComponentTiles : Nat := mentsuTileCount
private def maxWaitReadingComponents : Nat := standardHandMentsuCount + standardHandPairCount
private def componentTileKeyStride : Nat := tileKeyBase ^ maxComponentTiles
private def readingComponentKeyStride : Nat := WaitReadingComponentKind.count * componentTileKeyStride
private def readingWaitKeyStride : Nat := readingComponentKeyStride ^ maxWaitReadingComponents
private def abstractComponentKeyBase : Nat := WaitReadingComponentKind.count + keyDigitOffset
private def waitKeyStride : Nat := Tile.count

private def waitReadingComponentKey (component : WaitReadingComponentKind) : Nat :=
  WaitReadingComponentKind.all.idxOf component

private def concreteComponentKey (component : ConcreteWaitReadingComponent) : Nat :=
  waitReadingComponentKey component.kind * componentTileKeyStride +
    component.tiles.foldl
      (fun key tile => key * tileKeyBase + tile.orderKey + keyDigitOffset) 0

private def canonicalizeWaitReading
  (components : List ConcreteWaitReadingComponent) : List ConcreteWaitReadingComponent :=
  components.mergeSort fun first second =>
    concreteComponentKey first ≤ concreteComponentKey second

private def concreteWaitReadingKey (reading : ConcreteWaitReading) : Nat :=
  reading.wait.orderKey * readingWaitKeyStride +
    reading.components.foldl
      (fun key component => key * readingComponentKeyStride + concreteComponentKey component) 0

private def waitCoreKey (core : WaitCore) : Nat :=
  core.wait.orderKey * readingWaitKeyStride +
    core.components.foldl
      (fun key component => key * readingComponentKeyStride + concreteComponentKey component) 0

private def abstractWaitReadingKey (reading : AbstractWaitReading) : Nat :=
  reading.components.foldl
    (fun key component =>
      key * abstractComponentKeyBase + waitReadingComponentKey component + keyDigitOffset) 0 *
      waitKeyStride +
    reading.wait.orderKey

private def waitReadingCodeEntryKey (entry : WaitReadingCodeEntry) : Nat :=
  entry.code * waitKeyStride + entry.wait.orderKey

private def deduplicateAndSortBy {α : Type} [BEq α]
    (key : α → Nat) (values : List α) : List α :=
  values.eraseDups.mergeSort fun first second => key first ≤ key second

private def waitReadings (completion : WaitCompletion) :
    List (List ConcreteWaitReadingComponent) :=
  let rec selectCompletedChunk : List TileChunk → List (List ConcreteWaitReadingComponent)
    | [] => []
    | chunk :: rest =>
        let later := (selectCompletedChunk rest).map fun extraction =>
          completeComponent chunk :: extraction
        match componentAfterRemovingWait completion.wait chunk with
        | some incomplete =>
            (incomplete :: rest.map completeComponent) :: later
        | none => later
  selectCompletedChunk completion.winningChunks

/-- 発見済みの待ちと分割から、待ち牌ごとの具体的なReadingを列挙する。 -/
def concreteWaitReadings
    (completions : List WaitCompletion) : List ConcreteWaitReading :=
  let entries := completions.flatMap fun completion =>
      (waitReadings completion).map fun reading =>
        { wait := completion.wait
          components := canonicalizeWaitReading reading }
  deduplicateAndSortBy concreteWaitReadingKey entries

private def isCompletedMentsu (component : ConcreteWaitReadingComponent) : Bool :=
  component.kind == .shuntsu || component.kind == .koutsu

/--
1つの具体牌付きReadingを、待ち核の成分列と、そこから分離した完成面子に分ける。

順子 `.shuntsu` と刻子 `.koutsu` は `removedMentsu` に移し、それ以外の不完全部品は `core` に残す。
待ち牌 `wait` と各部品の具体的な牌種列は保持するため、後続処理は「どの完成面子を除いたか」を失わずに、
完成面子を除いた核成分列だけを比較できる。
この関数は1つのReadingを二分するだけであり、牌姿全体が可約か既約かは判定しない。

読むためのLean語彙: `structure`, `filter`, `fun`, `!`。
-/
def reduceWaitReading (reading : ConcreteWaitReading) : IrreducibleWaitReading :=
  { wait := reading.wait
    core := reading.components.filter fun component => !isCompletedMentsu component
    removedMentsu := reading.components.filter isCompletedMentsu }

/-- 発見済みのReadingを、完成面子を除いた待ち核へ正規化する。 -/
def irreducibleWaitReadings
    (completions : List WaitCompletion) : List IrreducibleWaitReading :=
  (concreteWaitReadings completions).map reduceWaitReading

/-- 発見済みの全Readingを待ち核集合へ正規化する。 -/
def waitCores (completions : List WaitCompletion) : List WaitCore :=
  irreducibleWaitReadings completions
    |>.map (fun reading => { wait := reading.wait, components := reading.core })
    |> deduplicateAndSortBy waitCoreKey

/-- 発見済み `WaitCompletion` から牌位置を忘れ、部品種別だけのReadingへ変換する。 -/
def abstractWaitReadings
    (completions : List WaitCompletion) : List AbstractWaitReading :=
  concreteWaitReadings completions
    |>.map (fun reading =>
      { wait := reading.wait
        components := reading.components.map (fun component => component.kind) })
    |> deduplicateAndSortBy abstractWaitReadingKey

/-- 発見済みWaitCompletionを、待ち牌ごとの素数積コードへ変換する。 -/
def waitReadingCodeEntries
    (completions : List WaitCompletion) : List WaitReadingCodeEntry :=
  abstractWaitReadings completions
    |>.map (fun reading =>
      { wait := reading.wait
        code := componentProduct reading.components })
    |> deduplicateAndSortBy waitReadingCodeEntryKey

/-- 発見済みWaitCompletionから計算した、待ち牌を残す抽象形コード。 -/
def abstractWaitReadingCodeWithWait
    (completions : List WaitCompletion) : List (Nat × Tile) :=
  waitReadingCodeEntries completions
    |>.map fun entry => (entry.code, entry.wait)

/-- 発見済みWaitCompletionから待ち牌を忘れ、抽象形コードだけを列挙する。 -/
def abstractWaitReadingCode (completions : List WaitCompletion) : List Nat :=
  waitReadingCodeEntries completions
    |>.map (fun entry => entry.code)
    |> deduplicateAndSortBy id

/-! ## 牌列から探索して符号化する便利関数 -/

def findConcreteWaitReadings (tiles : List Tile) : List ConcreteWaitReading :=
  concreteWaitReadings (WaitCompletionFinder.findWaitCompletions tiles)

/-- 牌列から、完成面子と分離した待ち核を列挙する。 -/
def findIrreducibleWaitReadings (tiles : List Tile) : List IrreducibleWaitReading :=
  irreducibleWaitReadings (WaitCompletionFinder.findWaitCompletions tiles)

/-- 牌列から得られる待ち核集合。 -/
def findWaitCores (tiles : List Tile) : List WaitCore :=
  waitCores (WaitCompletionFinder.findWaitCompletions tiles)

/-- 完成面子を1つ除いても待ち核集合が変わらないかを判定する。 -/
def canReduceMentsuPreservingWaitCores (tiles : List Tile) : Bool :=
  1 < tiles.length &&
    (mentsuReductions tiles).any fun remaining =>
      !(waitingTiles remaining).isEmpty && findWaitCores remaining == findWaitCores tiles

/-- 完成面子の除去後も待ち核集合が同じであること。 -/
def CanReduceMentsuPreservingWaitCores (tiles : List Tile) : Prop :=
  canReduceMentsuPreservingWaitCores tiles = true

instance (tiles : List Tile) : Decidable (CanReduceMentsuPreservingWaitCores tiles) := by
  unfold CanReduceMentsuPreservingWaitCores
  infer_instance

def findAbstractWaitReadings (tiles : List Tile) : List AbstractWaitReading :=
  abstractWaitReadings (WaitCompletionFinder.findWaitCompletions tiles)

def findWaitReadingCodeEntries (tiles : List Tile) : List WaitReadingCodeEntry :=
  waitReadingCodeEntries (WaitCompletionFinder.findWaitCompletions tiles)

def findAbstractWaitReadingCodeWithWait (tiles : List Tile) : List (Nat × Tile) :=
  abstractWaitReadingCodeWithWait (WaitCompletionFinder.findWaitCompletions tiles)

def findAbstractWaitReadingCode (tiles : List Tile) : List Nat :=
  abstractWaitReadingCode (WaitCompletionFinder.findWaitCompletions tiles)

/--
数牌1スートの既約な7枚待ち53形。最小ランクが1になるよう正規化している。
`m` を `p` や `s` に置き換えるか、ランク1--9を外れない範囲で平行移動しても、
同値な具体例が得られる。
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

private def insertAbstractWaitReadingClass (entry : String × List Nat) :
  List (List Nat × List String) → List (List Nat × List String)
  | [] => [(entry.2, [entry.1])]
  | current :: rest =>
      if current.1 == entry.2 then
        (current.1, current.2 ++ [entry.1]) :: rest
      else
        current :: insertAbstractWaitReadingClass entry rest

def irreducibleSevenTileAbstractWaitReadingClasses : List (List Nat × List String) :=
  irreducibleSingleSuitSevenTileExamples.foldl (fun classes entry =>
    insertAbstractWaitReadingClass (entry.1, findAbstractWaitReadingCode entry.2) classes) []

end WaitReadingCode
