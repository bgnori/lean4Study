import Mahjong.DirectWaitGeneration

/-!
# 麻雀計算モジュールの共通処理
-/

namespace MahjongComputations

/-- 牌種ごとの枚数を、物理上限より1大きい基数で符号化した多重集合キー。 -/
def tileMultisetKey (tiles : List Tile) : Nat :=
  Tile.all.foldl (fun key tile => key * (copiesPerTile + 1) + tiles.count tile) 0

/-- 各牌種を0枚から物理上限まで選ぶ合法牌多重集合の共通畳み込み。 -/
private def foldLegalTileMultisetsOfLength {α : Type}
    (empty : α) (combine : α → α → α)
    (onComplete : α) (prependCopies : Tile → Nat → α → α) :
    Nat → List Tile → α
  | length, [] =>
      if length == 0 then onComplete else empty
  | length, tile :: rest =>
      (List.range (Nat.min copiesPerTile length + 1)).foldl
        (fun result copies =>
          combine result (prependCopies tile copies
            (foldLegalTileMultisetsOfLength empty combine onComplete prependCopies
              (length - copies) rest)))
        empty
termination_by _ tiles => tiles.length

/-- 指定した牌種からなる、指定枚数の合法な牌多重集合。 -/
def legalTileMultisetsOfLength (length : Nat) (tiles : List Tile) : List (List Tile) :=
  foldLegalTileMultisetsOfLength [] List.append [[]]
    (fun tile copies tails => tails.map fun tail => List.replicate copies tile ++ tail)
    length tiles

/-- 指定した牌種からなる、指定枚数の合法な牌多重集合の個数。 -/
def countLegalTileMultisetsOfLength (length : Nat) (tiles : List Tile) : Nat :=
  foldLegalTileMultisetsOfLength 0 Nat.add 1 (fun _ _ count => count) length tiles

/-- 牌姿ごとに完成情報を集約する前の1件。 -/
structure WaitCompletionEntry where
  tiles : List Tile
  completion : WaitCompletion
deriving BEq, DecidableEq, Repr

/-- 同じ牌姿から得られた重複のない完成情報群。 -/
structure WaitCompletionGroup where
  tiles : List Tile
  completions : List WaitCompletion
deriving BEq, DecidableEq, Repr

private def waitCompletionEntryKeyLE
    (first second : WaitCompletionEntry) : Bool :=
  decide (tileMultisetKey first.tiles ≤ tileMultisetKey second.tiles)

private def insertCompletion
    (completion : WaitCompletion) (completions : List WaitCompletion) : List WaitCompletion :=
  if completions.contains completion then completions else completion :: completions

private def groupSortedWaitCompletionEntry
    (groups : List WaitCompletionGroup) (entry : WaitCompletionEntry) :
    List WaitCompletionGroup :=
  let key := tileMultisetKey entry.tiles
  match groups with
  | [] => [{ tiles := entry.tiles, completions := [entry.completion] }]
  | group :: rest =>
      if tileMultisetKey group.tiles == key then
        { group with completions := insertCompletion entry.completion group.completions } :: rest
      else
        { tiles := entry.tiles, completions := [entry.completion] } :: groups

/-- 完成情報を牌姿ごとにまとめ、同一牌姿内の重複を除く。 -/
def groupWaitCompletions (entries : List WaitCompletionEntry) : List WaitCompletionGroup :=
  entries.mergeSort waitCompletionEntryKeyLE
    |>.foldl groupSortedWaitCompletionEntry []

/-- 直接導出を、同じ牌姿から得られた完成情報群へまとめる。 -/
def groupWaitDerivations {mentsuCount : Nat}
    (derivations : List (DirectWaitGeneration.WaitDerivation mentsuCount)) :
    List WaitCompletionGroup :=
  derivations
    |>.map (fun derivation =>
      { tiles := DirectWaitGeneration.hand derivation
        completion := DirectWaitGeneration.completion derivation })
    |> groupWaitCompletions

/-- 完成情報群に現れる待ち牌を、初出順で重複なく取り出す。 -/
def waitsFromCompletions (completions : List WaitCompletion) : List Tile :=
  (completions.map fun completion => completion.wait).eraseDups

/-- 同じ待ち分解コード列を持つ牌姿の件数と代表例。 -/
structure WaitDecompositionCodeGroup where
  codes : List Nat
  count : Nat
  representativeTiles : List Tile
  representativeWaits : List Tile
deriving BEq, DecidableEq, Repr

/-- 待ち分解コード列が一致するグループへ牌姿を1件加える。 -/
def addWaitDecompositionCodeGroup
    (codes : List Nat) (tiles waits : List Tile) :
    List WaitDecompositionCodeGroup → List WaitDecompositionCodeGroup
  | [] => [{ codes, count := 1, representativeTiles := tiles, representativeWaits := waits }]
  | group :: rest =>
      if group.codes == codes then
        { group with count := group.count + 1 } :: rest
      else
        group :: addWaitDecompositionCodeGroup codes tiles waits rest

/-- 各値を待ち分解コード列でまとめ、件数と最初の代表例を保持する。 -/
def groupByWaitDecompositionCodes {α : Type}
    (codes : α → List Nat) (tiles waits : α → List Tile) (values : List α) :
    List WaitDecompositionCodeGroup :=
  values.foldl
    (fun groups value => addWaitDecompositionCodeGroup
      (codes value) (tiles value) (waits value) groups)
    []

/-- 自然数キーの度数表へ1件加える。 -/
def incrementCount (key : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(key, 1)]
  | entry :: rest =>
      if entry.1 == key then
        (entry.1, entry.2 + 1) :: rest
      else
        entry :: incrementCount key rest

/-- 自然数列を初出順の度数表へ変換する。 -/
def countOccurrences (values : List Nat) : List (Nat × Nat) :=
  values.foldl (fun counts value => incrementCount value counts) []

private def formatNumberedGroup
    (tiles : List Tile) (suit : Suit) (suffix : String) : String :=
  let digits := (List.ofFn fun rank : Rank => rank).flatMap fun rank =>
    List.replicate (tiles.count (.numbered suit rank)) (toString (rank.val + 1))
  if digits.isEmpty then "" else String.join digits ++ suffix

private def formatHonorGroup (tiles : List Tile) : String :=
  let digits := Honor.all.flatMap fun honor =>
    List.replicate (tiles.count (.honor honor)) (toString (honor.orderKey + 1))
  if digits.isEmpty then "" else String.join digits ++ "z"

/-- 牌種列をスートごとにまとめた省略表記へ変換する。 -/
def formatTiles (tiles : List Tile) : String :=
  String.join <| [
    formatNumberedGroup tiles .Manzu "m",
    formatNumberedGroup tiles .Pinzu "p",
    formatNumberedGroup tiles .Souzu "s",
    formatHonorGroup tiles
  ].filter fun group => !group.isEmpty

/-- 待ち分解コードグループをレポートのTSV行へ変換する。 -/
def formatWaitDecompositionCodeGroup (group : WaitDecompositionCodeGroup) : String :=
  String.intercalate "\t" [
    toString group.codes,
    toString (WaitDecompositionCode.waitDecompositionCodesKey group.codes),
    toString group.count,
    formatTiles group.representativeTiles,
    formatTiles group.representativeWaits
  ]

/-- 待ち牌種類数の度数をレポート行へ変換する。 -/
def formatWaitTileCount (counts : List (Nat × Nat)) (waitTileCount : Nat) : String :=
  let count := (counts.find? fun entry => entry.1 == waitTileCount).map Prod.snd |>.getD 0
  s!"{waitTileCount} wait tile kinds: {count}"

end MahjongComputations
