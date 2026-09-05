import Mahjong.Basic

/-!
# 牌パターン

このモジュールでは、待ち分類を構成する小さな部品を定義する。
`Toitsu`、`Shuntsu`、`MentsuCandidate` は、それぞれ必要な牌種列を `tiles` で返す。
和了構成部品 `WinningComponent` は、雀頭 `Toitsu` と面子候補 `MentsuCandidate` の直和として表す。
-/

/-!

順子は、開始位置を `Fin` で表す。`Fin n` は `0` 以上 `n` 未満の値なので、
存在しない開始位置を型で除外できる。
-/

/-- 完成面子を構成する牌の枚数。 -/
abbrev mentsuTileCount : Nat := 3

/-- 通常の最大手牌に含まれる面子数。 -/
abbrev standardHandMentsuCount : Nat := 4

/-- 通常形に含まれる雀頭の数。 -/
abbrev standardHandPairCount : Nat := 1

/-- 指定した面子数に対応する通常形聴牌の手牌枚数。 -/
def standardTenpaiHandSize (mentsuCount : Nat) : Nat :=
  mentsuCount * mentsuTileCount + standardHandPairCount

/-- 順子・嵌張ターツの開始位置数。 -/
abbrev shuntsuStartCount : Nat := numberedRankCount - 2

/-- 最初の順子開始位置。 -/
abbrev firstShuntsuStart : Nat := Rank.first.val

/-- 最後の順子開始位置。 -/
abbrev lastShuntsuStart : Nat := shuntsuStartCount - 1

/-- 順子・嵌張ターツの開始位置。 -/
abbrev ShuntsuStart := Fin shuntsuStartCount

namespace ShuntsuStart

/-!
## 順子・嵌張ターツの開始位置からランクを得る

順子や嵌張ターツは実際の1始まりから7始まりまでを扱う。
`firstRank`、`middleRank`、`lastRank` は、開始位置に対応する3つのランクを返す。
`isFirst` と `isLast` は、辺張判定で使う端の開始位置を見分ける補助である。
-/

/-- 順子の先頭ランク。 -/
def firstRank (start : ShuntsuStart) : Rank :=
  ⟨start.val, Nat.lt_trans start.isLt (by decide)⟩

/-- 順子の中央ランク。 -/
def middleRank (start : ShuntsuStart) : Rank :=
  ⟨start.val + 1, Nat.lt_trans (Nat.add_lt_add_right start.isLt 1) (by decide)⟩

/-- 順子の終端ランク。 -/
def lastRank (start : ShuntsuStart) : Rank :=
  ⟨start.val + 2, Nat.add_lt_add_right start.isLt 2⟩

/-- 最初の順子開始位置かどうか。 -/
def isFirst (start : ShuntsuStart) : Bool :=
  start.val == firstShuntsuStart

/-- 最後の順子開始位置かどうか。 -/
def isLast (start : ShuntsuStart) : Bool :=
  start.val == lastShuntsuStart

end ShuntsuStart

/-!
## 和了構成部品で使う小さな牌パターン

ここからは、麻雀上の部品をLeanのデータ構造として定義する。

- `Toitsu`: 同じ牌種2枚からなる対子。
- `Shuntsu`: 同じスートで連続する3枚からなる順子。
- `MentsuCandidate`: 通常形で完成面子として扱う候補。順子または刻子。

これらはそれぞれ `tiles` で必要な牌種列を返す。
-/

/-- 対子。同じ牌種2枚からなる。 -/
inductive Toitsu
| toitsu  (t: Tile)
deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Fintype

namespace Toitsu

/-!
## 対子と牌種列

`Toitsu.tiles` は、同じ牌種を2回並べた牌種列を返す。
-/

/-- 対子を構成する2枚の牌種列。 -/
def tiles : Toitsu → List Tile
  | .toitsu tile => [tile, tile]

example : (Toitsu.toitsu (.numbered .Manzu 4)).tiles.map (Tile.format .mpsz) = ["5m", "5m"] := rfl
example : (Toitsu.toitsu (.honor .White)).tiles.map (Tile.format .mpsz) = ["5z", "5z"] := rfl

end Toitsu

/-!
## 順子
-/
/-- 順子。数牌の同一スートで、連続する3ランクからなる。 -/
inductive Shuntsu
| shuntsu (suit : Suit) (start : ShuntsuStart)
deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Fintype

namespace Shuntsu

/-!
## 順子と牌種列

`Shuntsu.tiles` は、開始位置から先頭・中央・終端の3ランクを計算し、
同じスートの連続する3枚の牌種列を返す。
-/

/-- 順子を構成する3枚の牌種列。 -/
def tiles : Shuntsu → List Tile
  | .shuntsu suit start =>
      [.numbered suit start.firstRank,
       .numbered suit start.middleRank,
       .numbered suit start.lastRank]

example : (Shuntsu.shuntsu .Souzu ⟨0, by decide⟩).tiles.map (Tile.format .mpsz) = ["1s", "2s", "3s"] := rfl
example : (Shuntsu.shuntsu .Manzu ⟨6, by decide⟩).tiles.map (Tile.format .mpsz) = ["7m", "8m", "9m"] := rfl

end Shuntsu

/-!
## メンツ
-/
/-- 通常形で完成面子として扱う候補。順子または刻子。 -/
inductive MentsuCandidate
| shuntsu (shuntsu : Shuntsu)
| koutsu (t: Tile)
deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Fintype

namespace MentsuCandidate

/-!
## 完成面子候補と列挙

`MentsuCandidate` は、通常形で完成面子として扱う候補を順子または刻子として表す。
`candidates` は実行用に全順子候補と全刻子候補を並べ、`mem_candidates` がその列挙に
取りこぼしがないことを確認する。
-/

/-- 有限型として列挙できるすべての完成面子候補。 -/
noncomputable def all : List MentsuCandidate :=
  (Finset.univ : Finset MentsuCandidate).toList

/-- 実行用の完成面子候補列。全順子候補と全刻子候補を含む。 -/
def candidates : List MentsuCandidate :=
  (Suit.all.flatMap fun suit =>
    List.ofFn fun start : ShuntsuStart => MentsuCandidate.shuntsu (.shuntsu suit start)) ++
  Tile.all.map MentsuCandidate.koutsu

/--
任意の完成面子候補は、実行用候補列 `MentsuCandidate.candidates` に含まれる。

この定理は、完成面子候補を列挙して調べる処理が、順子候補と刻子候補を取りこぼさないことを保証する。
証明では候補を順子の場合と刻子の場合に分ける。順子の場合はスートと開始位置から作った順子候補列に
含まれることを示し、刻子の場合は `Tile.mem_all` を使って、刻子に使う牌種が標準牌種列に含まれることを示す。

読むためのLean語彙: `inductive`, `namespace`, `theorem`, `cases`, `rcases`, `simp`, `left`, `refine`, `?_`, `exact`, `∈`。
-/
theorem mem_candidates (mentsu : MentsuCandidate) :
    mentsu ∈ candidates := by
  cases mentsu with
  | shuntsu shuntsuPattern =>
      rcases shuntsuPattern with ⟨suit, start⟩
      simp only [candidates, List.mem_append, List.mem_flatMap]
      left
      refine ⟨suit, by cases suit <;> simp [Suit.all], ?_⟩
      exact List.mem_ofFn.mpr ⟨start, rfl⟩
  | koutsu tile =>
      simp [candidates, Tile.mem_all tile]

/-- 完成面子候補を構成する3枚の牌種列。 -/
def tiles : MentsuCandidate → List Tile
  | .shuntsu shuntsuPattern => shuntsuPattern.tiles
  | .koutsu tile => [tile, tile, tile]

example : (MentsuCandidate.koutsu (.numbered .Pinzu 6)).tiles.map (Tile.format .mpsz) = ["7p", "7p", "7p"] := rfl
example : (MentsuCandidate.koutsu (.honor .East)).tiles.map (Tile.format .mpsz) = ["1z", "1z", "1z"] := rfl

/-- 完成面子候補が順子であることを表す述語。 -/
def IsShuntsu : MentsuCandidate → Prop
  | .shuntsu _ => True
  | _ => False

/--
字牌を含む完成面子候補は順子ではない。

この定理は、順子が同じスートの連続する数牌だけからなる、という麻雀上の制約をLean上の
`MentsuCandidate` に対して確認する。候補が刻子なら順子ではない。候補が順子なら、
`Shuntsu.tiles` は数牌だけを返すため、字牌が含まれるという仮定と矛盾する。

読むためのLean語彙: `Prop`, `theorem`, `∈`, `¬`, `cases`, `simp`, `at`。
-/
theorem honor_not_in_shuntsu (candidate : MentsuCandidate) (honor : Honor)
    (honor_mem : Tile.honor honor ∈ candidate.tiles) : ¬candidate.IsShuntsu := by
  cases candidate with
  | koutsu tile => simp [IsShuntsu]
  | shuntsu shuntsuPattern =>
      cases shuntsuPattern
      simp [tiles, Shuntsu.tiles] at honor_mem

end MentsuCandidate

/-!
## 雀頭と完成面子を同じ和了構成部品として扱う

通常形の和了分割では、雀頭と完成面子をどちらも「完成した部品」として並べて扱う。
`WinningComponent` は、雀頭 `Toitsu` または完成面子候補 `MentsuCandidate` のどちらかを持つ型である。

`pair`、`shuntsu`、`koutsu` は、麻雀上の呼び名から `WinningComponent` を作る入口である。
`WinningComponent.tiles` は、どちらの部品であっても構成する牌種列を返す。
-/

/-- 通常形の和了分割に現れる和了構成部品。雀頭または完成面子。 -/
abbrev WinningComponent := Toitsu ⊕ MentsuCandidate

namespace WinningComponent

/-- 指定した牌種の雀頭を和了構成部品として作る。 -/
def pair (tile : Tile) : WinningComponent :=
  .inl (.toitsu tile)

/-- 指定した順子を和了構成部品として作る。 -/
def shuntsu (suit : Suit) (start : ShuntsuStart) : WinningComponent :=
  .inr (.shuntsu (.shuntsu suit start))

/-- 指定した牌種の刻子を和了構成部品として作る。 -/
def koutsu (tile : Tile) : WinningComponent :=
  .inr (.koutsu tile)

/-- 和了構成部品を構成する牌種列。 -/
def tiles : WinningComponent → List Tile
  | .inl pair => pair.tiles
  | .inr mentsu => mentsu.tiles

example : (WinningComponent.pair (.numbered .Manzu 4)).tiles.map (Tile.format .mpsz) = ["5m", "5m"] := rfl
example : (WinningComponent.shuntsu .Pinzu ⟨3, by decide⟩).tiles.map (Tile.format .mpsz) = ["4p", "5p", "6p"] := rfl
example : (WinningComponent.koutsu (.honor .Red)).tiles.map (Tile.format .mpsz) = ["7z", "7z", "7z"] := rfl

end WinningComponent
