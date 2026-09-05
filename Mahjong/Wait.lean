import Mahjong.Pattern

/-!
# 通常形聴牌の待ち抽出パターン

このモジュールでは、通常形聴牌から完成面子を分離した後に残る核成分列の形を
`WaitPattern` として表す。実際に待ちであることは `WaitCompletionFinder.IsWaitFor` が定める。

ここでいう待ち核は、待ち牌と核成分列の組である。`WaitPattern` はそのうち核成分列として
抽出できる形を表す。
可約・既約の判定は後続の `WaitReducibility` と `WaitDecompositionCode.CanReduceMentsuPreservingWaitCores` で扱う。
-/

/-!
## 既約な待ち核の抽出パターン

`WaitPattern` は、完成面子を取り除いたあとに残る核成分列の抽出パターンを表す。
ここでは麻雀一般の「待ち読み」という語を避け、抽出に使うデータ構造として扱う。
実際に待ちであることの証明は `WaitCompletionFinder.IsWaitFor` が担当する。

- `tanki`: 単騎として扱う1枚。
- `toitsuRyanmen`: 対子と両面ターツからなる4枚の待ち核。
- `toitsuKanchan`: 対子と嵌張ターツからなる4枚の待ち核。
- `toitsuPenchan`: 対子と辺張ターツからなる4枚の待ち核。
- `shanpon`: 2つの対子からなる4枚の待ち核。

完成面子はこの型に含めず、抽出過程の `HandExtraction.mentsuThen` で表す。
具体牌付きの核成分列は `WaitCoreExtraction.core` に保持する。待ち牌と核成分列を組にして、
除去した完成面子の文脈を忘れて比較する形は `WaitCore` で表す。

`WaitPattern.tiles` は、その抽出パターンで必要になる牌種列を返す。
-/

/-- 完成面子を除いたあとに残る核成分列の抽出パターン。 -/
inductive WaitPattern
| tanki (tanki : Tanki)
| toitsuRyanmen (toitsu : Toitsu) (suit : Suit) (start : RyanmenStart)
| toitsuKanchan (toitsu : Toitsu) (suit : Suit) (start : ShuntsuStart)
| toitsuPenchan (toitsu : Toitsu) (suit : Suit) (high : Bool)
| shanpon (first second : Toitsu)
deriving BEq, DecidableEq, Repr, Fintype

namespace WaitPattern

/-!
## 核成分列と牌種列

`WaitPattern.tiles` は、各抽出パターンが要求する牌種列を返す。
たとえば対子と両面ターツの核成分列なら、対子の2枚に両面ターツの2枚を連結する。
`HasTilePattern` のインスタンスにより、核成分列の抽出パターンも共通の物理牌取り出し処理に渡せる。
-/

/-- 有限型として列挙できるすべての抽出候補。 -/
noncomputable def all : List WaitPattern :=
  (Finset.univ : Finset WaitPattern).toList

/-- 抽出候補が要求する牌種列。 -/
def tiles : WaitPattern → List Tile
  | .tanki single => single.tiles
  | .toitsuRyanmen toitsu suit start => toitsu.tiles ++ (Taatsu.ryanmen suit start).tiles
  | .toitsuKanchan toitsu suit start => toitsu.tiles ++ (Taatsu.kanchan suit start).tiles
  | .toitsuPenchan toitsu suit high => toitsu.tiles ++ (Taatsu.penchan suit high).tiles
  | .shanpon first second => first.tiles ++ second.tiles

example : (WaitPattern.tanki (.tanki (.honor .East))).tiles.map (Tile.format .mpsz) = ["1z"] := rfl
example : (WaitPattern.toitsuRyanmen (.toitsu (.numbered .Manzu 4)) .Manzu ⟨0, by decide⟩).tiles.map (Tile.format .mpsz) = ["5m", "5m", "2m", "3m"] := rfl
example : (WaitPattern.toitsuKanchan (.toitsu (.honor .White)) .Pinzu ⟨2, by decide⟩).tiles.map (Tile.format .mpsz) = ["5z", "5z", "3p", "5p"] := rfl
example : (WaitPattern.toitsuPenchan (.toitsu (.honor .Red)) .Souzu true).tiles.map (Tile.format .mpsz) = ["7z", "7z", "8s", "9s"] := rfl
example : (WaitPattern.shanpon (.toitsu (.numbered .Pinzu 1)) (.toitsu (.honor .East))).tiles.map (Tile.format .mpsz) = ["2p", "2p", "1z", "1z"] := rfl

instance : HasTilePattern WaitPattern where
  tiles := WaitPattern.tiles

noncomputable def take (extraction : WaitPattern) (chunk : Chunk) :
    Option (List PhysicalTile × Finset PhysicalTile) :=
  HasTilePattern.take extraction chunk

end WaitPattern
