import Mahjong.Pattern

/-!
# 通常形聴牌の待ち分類

このモジュールでは、通常形聴牌の終端部をどの形として抽出するかを `WaitPattern`、
麻雀上の分類語彙を `WaitKind` として表す。実際に待ちであることは
`WaitCompletionFinder.IsWaitFor` が定め、分類は `WaitCompletion` の解析結果から計算する。
-/

/-!
## 待ち終端の抽出パターン

`WaitPattern` は、完成面子を取り除いたあとに残る既約な待ちの核を表す。
ここでは麻雀一般の「待ち読み」という語を避け、抽出に使うデータ構造として扱う。
実際に待ちであることの証明は `WaitCompletionFinder.IsWaitFor` が担当する。

- `tanki`: 単騎として扱う1枚。
- `toitsuRyanmen`: 対子と両面ターツからなる4枚終端。
- `toitsuKanchan`: 対子と嵌張ターツからなる4枚終端。
- `toitsuPenchan`: 対子と辺張ターツからなる4枚終端。
- `shanpon`: 2つの対子からなる4枚終端。

完成面子はこの型に含めず、抽出過程の `HandExtraction.mentsuThen` で表す。

`WaitPattern.tiles` は、その抽出パターンで必要になる牌種列を返す。
-/

/-- 完成面子を除いた待ちの既約核を取り出す方法。 -/
inductive WaitPattern
| tanki (tanki : Tanki)
| toitsuRyanmen (toitsu : Toitsu) (suit : Suit) (start : RyanmenStart)
| toitsuKanchan (toitsu : Toitsu) (suit : Suit) (start : ShuntsuStart)
| toitsuPenchan (toitsu : Toitsu) (suit : Suit) (high : Bool)
| shanpon (first second : Toitsu)
deriving BEq, DecidableEq, Repr, Fintype

namespace WaitPattern

/-!
## 待ち終端の抽出パターンと牌種列

`WaitPattern.tiles` は、各抽出パターンが要求する牌種列を返す。
たとえば対子と両面ターツの終端なら、対子の2枚に両面ターツの2枚を連結する。
`HasTilePattern` のインスタンスにより、待ち終端の抽出パターンも共通の物理牌取り出し処理に渡せる。
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

/-- 通常形聴牌で現れる待ちの種類。 -/
inductive WaitKind
| tanki
| toitsuRyanmen
| toitsuKanchan
| toitsuPenchan
| shanpon
| nobetan
| kuttsukiRyanmen
| kuttsukiKanchan
| kuttsukiPenchan
deriving BEq, DecidableEq, Repr, Fintype

namespace WaitKind

/-- `WaitKind` の明示的な列挙。ドキュメント上の分類表としても使う。 -/
def all : List WaitKind :=
  [.tanki,
   .toitsuRyanmen,
   .toitsuKanchan,
   .toitsuPenchan,
   .shanpon,
   .nobetan,
   .kuttsukiRyanmen,
   .kuttsukiKanchan,
   .kuttsukiPenchan]

/--
すべての待ち分類名は標準列挙 `WaitKind.all` に含まれる。

この定理は、通常形聴牌で使う分類語彙の一覧に抜けがないことを保証する。
証明は `WaitKind` の各分類名に場合分けし、それぞれが明示的な一覧に含まれることを示す。

読むためのLean語彙: `namespace`, `theorem`, `cases`, `<;>`, `simp`, `[...]`, `∈`。
-/
theorem exhaustive (kind : WaitKind) : kind ∈ all := by
  cases kind <;> simp [all]

end WaitKind

/-- 分解が一意か、複数の読みを持つか。 -/
inductive WaitAmbiguity
| noAmbiguity
| ambiguous
deriving BEq, DecidableEq, Repr, Fintype

/-- 完成面子を取り除いてより小さい待ちへ還元できるか。 -/
inductive WaitReducibility
| reducible
| irreducible
deriving BEq, DecidableEq, Repr, Fintype

/-- 待ち名だけから決まる分類ラベル。既約性は牌姿に対して別途計算する。 -/
structure WaitClassification where
  kind : WaitKind
  ambiguity : WaitAmbiguity
deriving BEq, DecidableEq, Repr

/-- 待ちの分類語彙に対応する性質。 -/
def WaitKind.classification : WaitKind → WaitClassification
  | .tanki =>
    ⟨.tanki, .noAmbiguity⟩
  | .toitsuRyanmen =>
    ⟨.toitsuRyanmen, .noAmbiguity⟩
  | .toitsuKanchan =>
    ⟨.toitsuKanchan, .noAmbiguity⟩
  | .toitsuPenchan =>
    ⟨.toitsuPenchan, .noAmbiguity⟩
  | .shanpon =>
    ⟨.shanpon, .noAmbiguity⟩
  | .nobetan =>
    ⟨.nobetan, .ambiguous⟩
  | .kuttsukiRyanmen =>
    ⟨.kuttsukiRyanmen, .ambiguous⟩
  | .kuttsukiKanchan =>
    ⟨.kuttsukiKanchan, .ambiguous⟩
  | .kuttsukiPenchan =>
    ⟨.kuttsukiPenchan, .ambiguous⟩

/-- この分類が複数の自然な読みを持つか。 -/
def WaitKind.ambiguity (kind : WaitKind) : WaitAmbiguity :=
  kind.classification.ambiguity
