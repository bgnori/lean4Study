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

/--
通常形の和了分割に現れる完成部品から、指定した待ち牌を1枚除いたときに見える不完全部品の種別を返す。

同種2枚の対子から1枚除けば単騎、同種3枚の刻子から1枚除けば対子になる。
順子では、除く位置と端の順子かどうかから両面・嵌張・辺張を区別する。
指定牌がその和了分割の完成部品を構成しない場合は `none` を返す。
-/
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

      example : componentKindAfterRemovingWait
        (.numbered .Manzu 4) (TileChunk.pair (.numbered .Manzu 4)) = some .tanki := rfl

      example : componentKindAfterRemovingWait
        (.numbered .Pinzu 6) (TileChunk.koutsu (.numbered .Pinzu 6)) = some .toitsu := rfl

      example : componentKindAfterRemovingWait
        (.numbered .Souzu 1) (TileChunk.shuntsu .Souzu ⟨1, by decide⟩) = some .ryanmen := rfl

      example : componentKindAfterRemovingWait
        (.numbered .Souzu 2) (TileChunk.shuntsu .Souzu ⟨1, by decide⟩) = some .kanchan := rfl

      example : componentKindAfterRemovingWait
        (.numbered .Souzu 2) (TileChunk.shuntsu .Souzu ⟨0, by decide⟩) = some .penchan := rfl

/--
完成部品から指定した待ち牌を1枚除き、種別と残った牌種列を持つ具体的な不完全部品を作る。

`componentKindAfterRemovingWait` が `some kind` を返した場合だけ、完成部品の牌種列から
待ち牌を最初の1枚だけ除き、`ConcreteWaitReadingComponent` にまとめる。
指定牌を除けず種別が `none` の場合は、この関数も `none` を返す。
-/
private def componentAfterRemovingWait (wait : Tile) (chunk : TileChunk) :
    Option ConcreteWaitReadingComponent :=
  (componentKindAfterRemovingWait wait chunk).map fun kind =>
    { kind, tiles := chunk.tiles.erase wait }

example : componentAfterRemovingWait
    (.numbered .Manzu 4) (TileChunk.pair (.numbered .Manzu 4)) =
      some { kind := .tanki, tiles := [.numbered .Manzu 4] } := rfl

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

/--
1つの待ち牌と和了分割から、待ち牌を除く完成部品の選び方をすべて列挙する。

各結果では、分割中の完成部品をちょうど1つ選んで `componentAfterRemovingWait` で不完全部品へ変え、
それ以外は `completeComponent` で完成した種別のまま残す。指定牌を除けない部品は選択肢にせず、
同じ待ち牌を除ける部品が複数あれば、除去元ごとに別のReadingを作る。
-/
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

example : waitReadings
    { wait := .numbered .Manzu 4
      winningChunks :=
        [TileChunk.pair (.numbered .Manzu 4), TileChunk.shuntsu .Pinzu ⟨0, by decide⟩] } =
    [[{ kind := .tanki, tiles := [.numbered .Manzu 4] },
      { kind := .shuntsu, tiles :=
        [.numbered .Pinzu 0, .numbered .Pinzu 1, .numbered .Pinzu 2] }]] := rfl

/--
発見済みの待ちと和了分割をすべて処理し、待ち牌ごとの具体牌付きReadingを正規化して列挙する。

各 `WaitCompletion` に `waitReadings` を適用し、待ち牌と部品列を `ConcreteWaitReading` にまとめる。
部品列を一定の順序に並べた後、全completionから得た同一Readingの重複を除いて結果全体も整列する。
そのため、和了分割内の部品順や同じcompletionの重複は、返り値を変えない。
-/
def concreteWaitReadings
    (completions : List WaitCompletion) : List ConcreteWaitReading :=
  let entries := completions.flatMap fun completion =>
      (waitReadings completion).map fun reading =>
        { wait := completion.wait
          components := canonicalizeWaitReading reading }
  deduplicateAndSortBy concreteWaitReadingKey entries

example : concreteWaitReadings
    [{ wait := .numbered .Manzu 4
       winningChunks :=
         [TileChunk.shuntsu .Pinzu ⟨0, by decide⟩, TileChunk.pair (.numbered .Manzu 4)] },
     { wait := .numbered .Manzu 4
       winningChunks :=
         [TileChunk.pair (.numbered .Manzu 4), TileChunk.shuntsu .Pinzu ⟨0, by decide⟩] }] =
    [{ wait := .numbered .Manzu 4
       components :=
         [{ kind := .tanki, tiles := [.numbered .Manzu 4] },
          { kind := .shuntsu, tiles :=
            [.numbered .Pinzu 0, .numbered .Pinzu 1, .numbered .Pinzu 2] }] }] := by
  native_decide

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

/--
発見済みの全Readingから、比較可能な待ち核集合を作る。

各 `IrreducibleWaitReading` から `removedMentsu` を忘れ、待ち牌 `wait` と核成分列 `core` だけを
`WaitCore` に残す。同じ待ち核が複数の和了分割から得られても1件として扱えるよう重複を除き、
待ち牌と核成分列から作るキーの順に整列する。

返り値は `List WaitCore` だが、重複がなく順序も正規化されているため、待ち核の有限集合として比較できる。
読むためのLean語彙: `map`, `fun`, `|>`。
-/
def waitCores (completions : List WaitCompletion) : List WaitCore :=
  irreducibleWaitReadings completions
    |>.map (fun reading => { wait := reading.wait, components := reading.core })
    |> deduplicateAndSortBy waitCoreKey

/--
発見済みの具体牌付きReadingから各部品の牌種列を忘れ、部品種別だけのReadingへ変換する。

待ち牌 `wait` は保持し、各 `ConcreteWaitReadingComponent` は `kind` だけに写す。
具体牌が異なっても待ち牌と部品種別列が同じReadingは重複を除き、一定の順序に整列する。
この段階では部品種別列をまだ数値コードには変換しない。
-/
def abstractWaitReadings
    (completions : List WaitCompletion) : List AbstractWaitReading :=
  concreteWaitReadings completions
    |>.map (fun reading =>
      { wait := reading.wait
        components := reading.components.map (fun component => component.kind) })
    |> deduplicateAndSortBy abstractWaitReadingKey

example : abstractWaitReadings
    [{ wait := .numbered .Manzu 4
       winningChunks :=
         [TileChunk.pair (.numbered .Manzu 4), TileChunk.shuntsu .Pinzu ⟨0, by decide⟩] },
     { wait := .numbered .Manzu 4
       winningChunks :=
         [TileChunk.pair (.numbered .Manzu 4), TileChunk.shuntsu .Pinzu ⟨3, by decide⟩] }] =
    [{ wait := .numbered .Manzu 4, components := [.tanki, .shuntsu] }] := by
  native_decide

/--
抽象Readingの部品種別列を素数積へ変換し、待ち牌ごとのコードとして列挙する。

各部品種別に割り当てた素数をすべて掛けるため、コードは部品順を忘れる一方、
各種別が現れる個数を素因数の指数として保持する。待ち牌はコードと別のフィールドに残し、
同じ待ち牌とコードの重複を除いて一定の順序に整列する。
-/
def waitReadingCodeEntries
    (completions : List WaitCompletion) : List WaitReadingCodeEntry :=
  abstractWaitReadings completions
    |>.map (fun reading =>
      { wait := reading.wait
        code := componentProduct reading.components })
    |> deduplicateAndSortBy waitReadingCodeEntryKey

example : waitReadingCodeEntries
    [{ wait := .numbered .Manzu 4
       winningChunks :=
         [TileChunk.pair (.numbered .Manzu 4), TileChunk.shuntsu .Pinzu ⟨0, by decide⟩] }] =
    [{ wait := .numbered .Manzu 4, code := 26 }] := by
  native_decide

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

/--
完成面子を1つ除いても、同じ待ち核集合を持つ聴牌形が残るかを判定する。

`mentsuReductions tiles` が列挙する各除去候補について、除去後にも待ち牌があり、かつ
`findWaitCores remaining` が元の `findWaitCores tiles` と一致するものが1つでもあるかを調べる。
待ち牌が残るという条件により、たまたま空の待ち核集合どうしが一致する場合は可約とみなさない。

`1 < tiles.length` は、完成面子を含み得ない1枚単騎を除外するための入口条件である。
読むためのLean語彙: `Bool`, `&&`, `!`, `List.any`, `==`。
-/
def canReduceMentsuPreservingWaitCores (tiles : List Tile) : Bool :=
  1 < tiles.length &&
    (mentsuReductions tiles).any fun remaining =>
      !(waitingTiles remaining).isEmpty && findWaitCores remaining == findWaitCores tiles

/--
待ち核集合を保ったまま完成面子を除去できることを表す命題。

実行用のBool判定 `canReduceMentsuPreservingWaitCores` が `true` を返すことを `Prop` として包む。
新しい探索条件を加える定義ではなく、同じ判定結果を定理の仮定や結論に使える形で公開する。
-/
def CanReduceMentsuPreservingWaitCores (tiles : List Tile) : Prop :=
  canReduceMentsuPreservingWaitCores tiles = true

/-- Bool判定との等式により、可約性の命題を条件分岐や計算で決定できるようにする。 -/
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
