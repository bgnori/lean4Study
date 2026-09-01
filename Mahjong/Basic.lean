import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-!
# 麻雀牌の基礎定義

このモジュールでは、以降の待ち分類で使う最小限のドメインモデルを定義する。
牌種としての `Tile` と、同じ牌種が4枚あることを表す `PhysicalTile` を分けることで、
「3mという種類」と「3mの1枚目」のような区別を Lean の型で表せるようにする。

待ちの解析ロジックの多くは牌種 `Tile` の列を扱う。一方、実際の手牌から牌を取り出す
処理では重複を扱う必要があるため、`PhysicalTile` と `Finset` を使う。
-/


/-!
 ## 数牌の定義
 -/
/-- 数牌のランク数。 -/
abbrev numberedRankCount : Nat := 9

/-- 数牌のランク。`0` から `8` が、それぞれ実際の `1` から `9` に対応する。 -/
 abbrev Rank := Fin numberedRankCount

/-- `Rank` を自然数リテラルで書くためのインスタンス。 -/
 instance (n : Nat) [ofNat : OfNat (Fin numberedRankCount) n] : OfNat Rank n where
   ofNat := (OfNat.ofNat n : Fin numberedRankCount)

namespace Rank

/-- 最初の数牌ランク。 -/
def first : Rank := ⟨0, by decide⟩

/-- 2番目の数牌ランク。 -/
def second : Rank := ⟨1, by decide⟩

/-- 最後から2番目の数牌ランク。 -/
def penultimate : Rank := ⟨numberedRankCount - 2, by decide⟩

/-- 最後の数牌ランク。 -/
def last : Rank := ⟨numberedRankCount - 1, by decide⟩

end Rank

/-- 数牌の3種類のスート。 -/
 inductive Suit
 | Manzu
 | Pinzu
 | Souzu
deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Fintype

namespace Suit

/-- 数牌の全スートを標準順で並べたリスト。 -/
def all : List Suit := [.Manzu, .Pinzu, .Souzu]

/-- 数牌のスート数。 -/
def count : Nat := all.length

/-- 標準列挙順に対応するスートのキー。 -/
def orderKey (suit : Suit) : Nat :=
  all.idxOf suit

end Suit


/-!
 ## 字牌の定義
 -/
/-- 字牌の7種類。 -/
 inductive Honor
 | East
 | South
 | West
 | North
 | White
 | Green
 | Red
deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Fintype

namespace Honor

/-- すべての字牌を標準順で並べたリスト。 -/
def all : List Honor := [.East, .South, .West, .North, .White, .Green, .Red]

/-- 字牌の種類数。 -/
def count : Nat := all.length

/-- 標準列挙順に対応する字牌のキー。 -/
def orderKey (honor : Honor) : Nat :=
  all.idxOf honor

end Honor

/-!
 ## 麻雀牌の種類の定義 -> 萬子・筒子・索子と字牌
 -/
/-- 牌種。数牌はスートとランク、字牌は `Honor` で表す。 -/
 inductive Tile
 | numbered(suit : Suit) (rank : Rank )
 | honor(h : Honor )
deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Fintype

namespace Tile

/-- 数牌の牌種数。 -/
def numberedCount : Nat := Suit.count * numberedRankCount

/-- 牌種の総数。 -/
def count : Nat := numberedCount + Honor.count

/-- 指定したスートとランク列から数牌列を作る。 -/
def numberedTiles (suit : Suit) (ranks : List Rank) : List Tile :=
  ranks.map (.numbered suit)

/-- 34種類すべての牌種を標準順で並べたリスト。 -/
def all : List Tile :=
  (Suit.all.flatMap fun suit =>
    List.ofFn fun rank : Rank => Tile.numbered suit rank) ++
  Honor.all.map .honor

/--
すべての牌種は標準列挙 `Tile.all` に含まれる。

この定理は、以降の網羅的な探索や分類が参照する「34種類の牌の一覧」に
抜けがないことを保証する小さな土台である。証明は `Tile` を数牌と字牌に分け、
それぞれが対応する一覧に含まれることを示す。

読むためのLean語彙: `namespace`, `theorem`, `cases`, `simp`, `left`, `exact`, `∈`。
-/
theorem mem_all (tile : Tile) : tile ∈ all := by
  cases tile with
  | numbered suit rank =>
    simp only [all, List.mem_append, List.mem_flatMap]
    left
    exact ⟨suit, by cases suit <;> simp [Suit.all], List.mem_ofFn.mpr ⟨rank, rfl⟩⟩
  | honor honor =>
      cases honor <;> simp [all, Honor.all]

/-- 標準列挙順に対応する牌種のキー。 -/
def orderKey : Tile → Nat
  | Tile.numbered suit rank =>
      Suit.orderKey suit * numberedRankCount + rank.val
  | Tile.honor honorTile => numberedCount + Honor.orderKey honorTile

end Tile

/-!
 ## セットの定義
-/
/-- すべての牌種。 -/
def tileTypes : Finset Tile :=
  Tile.all.toFinset

/-- 同じ牌種ごとの物理牌の枚数。 -/
abbrev copiesPerTile : Nat := 4

/-- 山を構成する物理牌の総数。 -/
abbrev deckSize : Nat := Tile.count * copiesPerTile

/-- 物理的な1枚の牌。同じ牌種が4枚あることを `Fin 4` で区別する。 -/
abbrev PhysicalTile := Tile × Fin copiesPerTile

/-- 136枚すべての物理牌からなる山。 -/
def deck : Finset PhysicalTile :=
  Finset.univ

/--
麻雀牌の山は `deckSize` 枚、つまり34種類それぞれを `copiesPerTile` 枚ずつ含む。

この定理は、物理牌として扱う山の枚数が通常の麻雀牌の総数と一致することを保証する。
証明では `deck` の定義を展開し、有限型 `PhysicalTile` 全体の個数が `Tile.count * copiesPerTile`
になることを確認する。

読むためのLean語彙: `abbrev`, `Finset`, `.card`, `theorem`, `simp`, `rfl`。
-/
theorem deck_cardinality : deck.card = deckSize := by
  simp [deck]
  rfl

/--
まだ取り出せる物理牌の有限集合。

`nonempty` を持たせることで、空集合ではない牌集合だけを `Chunk` として扱う。
-/
structure Chunk where
  tiles : Finset PhysicalTile
  nonempty : tiles.Nonempty

namespace Chunk

/-- `chunk` から指定した物理牌を1枚取り出し、取り出した牌と残りを返す。 -/
def take (chunk : Chunk) (tile : { pt : PhysicalTile // pt ∈ chunk.tiles }) :
    PhysicalTile × Finset PhysicalTile :=
  (tile, chunk.tiles.erase tile)

@[simp]
theorem take_fst (chunk : Chunk) (tile : { pt : PhysicalTile // pt ∈ chunk.tiles }) :
    (chunk.take tile).1 = tile := rfl

@[simp]
theorem take_snd_not_mem (chunk : Chunk) (tile : { pt : PhysicalTile // pt ∈ chunk.tiles }) :
    tile.1 ∉ (chunk.take tile).2 := by
  simp [take]

noncomputable def takeTileFrom (tiles : Finset PhysicalTile) (wanted : Tile) :
    Option (PhysicalTile × Finset PhysicalTile) :=
  match tiles.toList.find? (fun tile => tile.1 == wanted) with
  | some tile => some (tile, tiles.erase tile)
  | none => none

/--
指定された牌種列に対応する物理牌を、有限集合から順に取り出す。

必要な牌が足りない場合は `none` を返す。成功時は、取り出した物理牌の列と残りの集合を返す。
-/
noncomputable def takeTilesFrom :
    Finset PhysicalTile → List Tile → Option (List PhysicalTile × Finset PhysicalTile)
  | tiles, [] => some ([], tiles)
  | tiles, wanted :: wantedTiles => do
      let (tile, remaining) ← takeTileFrom tiles wanted
      let (taken, rest) ← takeTilesFrom remaining wantedTiles
      pure (tile :: taken, rest)

noncomputable def takeTiles (chunk : Chunk) (wanted : List Tile) :
    Option (List PhysicalTile × Finset PhysicalTile) :=
  takeTilesFrom chunk.tiles wanted

end Chunk

/-- 「この型の値は、対応する牌種列を持つ」ことを表す型クラス。 -/
class HasTilePattern (α : Type) where
  tiles : α → List Tile

namespace HasTilePattern

noncomputable def take {α : Type} [HasTilePattern α] (pattern : α) (chunk : Chunk) :
    Option (List PhysicalTile × Finset PhysicalTile) :=
  chunk.takeTiles (HasTilePattern.tiles pattern)

end HasTilePattern

/-!
 # 麻雀牌の表記
 a) unicode で表す
 b) mpsz
 -/

/-- 牌の表示形式。`mpsz` は `123m55p` のような牌譜でよく使われる表記。 -/
inductive TileFormat
| unicode
| mpsz
deriving BEq, DecidableEq, Repr

namespace Tile

private def mpszSuffix : Suit → String
| .Manzu => "m"
| .Pinzu => "p"
| .Souzu => "s"

private def honorMpszRank (honor : Honor) : Nat :=
  Honor.orderKey honor + 1

private def numberedUnicodeOffset : Suit → Nat
| .Manzu => 0x1F007
| .Pinzu => 0x1F019
| .Souzu => 0x1F010

private def Honor.unicode : Honor → String
| .East => "🀀"
| .South => "🀁"
| .West => "🀂"
| .North => "🀃"
| .White => "🀆"
| .Green => "🀅"
| .Red => "🀄"

/-- 1つの牌種を指定された形式の文字列に変換する。 -/
def format (output : TileFormat) : Tile → String
| .numbered suit rank =>
  match output with
  | .unicode => String.singleton (Char.ofNat (numberedUnicodeOffset suit + rank.val))
  | .mpsz => s!"{rank.val + 1}{mpszSuffix suit}"
| .honor h =>
  match output with
  | .unicode => Honor.unicode h
  | .mpsz => s!"{honorMpszRank h}z"

example : format .unicode (.numbered .Manzu 0) = "🀇" := rfl
example : format .mpsz (.numbered .Pinzu 8) = "9p" := rfl
example : format .unicode (.honor .Red) = "🀄" := rfl
example : format .mpsz (.honor .White) = "5z" := rfl

end Tile
