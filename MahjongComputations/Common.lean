import Mahjong.DirectWaitGeneration

/-!
# 麻雀計算モジュールの共通処理
-/

namespace MahjongComputations

/-- 牌種ごとの枚数を、物理上限より1大きい基数で符号化した多重集合キー。 -/
def tileMultisetKey (tiles : List Tile) : Nat :=
  Tile.all.foldl (fun key tile => key * (copiesPerTile + 1) + tiles.count tile) 0

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

end MahjongComputations
