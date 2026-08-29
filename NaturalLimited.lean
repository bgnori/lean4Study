import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.DeriveFintype

/-!
# 有限型としてのトランプ

このファイルでは、`Suit`、`Rank`、`Card` を有限型として定義し、
`Finset.univ` によって「すべてのカードからなる有限集合」`deck` を作る。

このコメントは Lean の module doc comment である。通常の `--` コメントと違い、
`/-! ... -/` や `/-- ... -/` は doc-gen 系のツールでドキュメントとして抽出できる。
-/


-- proof 2 * 3 < 10
theorem two_mul_three_lt_ten : 2 * 3 < 10 := by
  decide

-- Fin 3 の要素がかならず3未満であることを示せ。
theorem fin3_lt_three (x : Fin 3) : x.val < 3 := by
  exact x.is_lt
#check Fin 3
#check Fin.val
#print Fin

theorem ex3 : Finset.card ({1, 2, 3} : Finset Nat ) = 3 := by
  decide

#check Finset
#check Finset.card

/--
トランプのスートを表す有限型。

`inductive` によって、`Suit` の値は `spade`、`heart`、`diamond`、`club` の
4つだけであると定義している。

`deriving` は、Lean に必要なインスタンスを自動生成させる指定である。

* `BEq`: `==` による真偽値としての等値判定を使えるようにする。
* `DecidableEq`: 命題 `a = b` が判定可能であることを Lean に教える。
* `Repr`: `#eval` などで値を表示しやすくする。
* `Fintype`: この型の全要素を有限個として列挙できることを Lean に教える。

ここで `Fintype` があるため、後で `Finset.univ : Finset Suit` のように
「すべてのスートからなる有限集合」を作れる。
-/
inductive Suit
  | spade | heart | diamond | club
  deriving BEq, DecidableEq, Repr, Fintype

/--
カードのランクを表す型。

`Fin 13` は「`13` 未満であることの証明を持った自然数」の型で、
値としては `0, 1, ..., 12` の13通りを持つ。

したがって `Rank` は13個の値を持つ有限型として扱える。
-/
def Rank := Fin 13

/-
`Rank` は定義上 `Fin 13` なので、`Fin 13` から各種インスタンスを導出する。

これにより、`Rank` も等値判定・表示・有限列挙ができる型として扱える。
-/
deriving instance BEq, DecidableEq, Repr, Fintype for Rank

/--
1枚のカードを表す構造体。

カードは `suit : Suit` と `rank : Rank` の組である。
`Suit` は4通り、`Rank` は13通りなので、`Card` は全体で
`4 * 13 = 52` 通りの値を持つ。

`deriving Fintype` により、Lean は `Card` の全要素を列挙できる。
直観的には、すべての `Suit` とすべての `Rank` の組み合わせを作っている。
-/
structure Card where
  suit : Suit
  rank : Rank
  deriving BEq, DecidableEq, Repr, Fintype

/--
すべてのカードからなる有限集合。

`Finset.univ` は、ある型に `Fintype` インスタンスがあるとき、
その型の全要素からなる有限集合を返す。

ここでは `Card` に `Fintype` があるので、`deck` は52枚すべてのカードを含む。
-/
def deck : Finset Card := Finset.univ

/--
`deck` の要素数が52であること。

`rfl` は「両辺を定義展開・簡約した結果が同じなら証明する」タクティクである。
ここでは `deck` が `Finset.univ` であり、`Card` が4通りの `Suit` と13通りの
`Rank` の組として有限列挙できるため、`Finset.card deck` は計算によって `52` まで
簡約される。したがって Lean から見ると、この等式は定義上 `52 = 52` になり、
`rfl` で閉じられる。

同じ証明は次のように `decide` でも書ける。

```lean
theorem deck_cardinality' : Finset.card deck = 52 := by
  decide
```

`decide` は、命題が判定可能なときに実際に計算して真偽を決めるタクティクである。
今回の命題は自然数の等号なので判定可能であり、左辺を計算すると `52` になるため、
`decide` も `52 = 52` が真であることを確認して証明を作る。

まとめると、`rfl` は「定義上同じになる」ことを使い、`decide` は
「判定可能な命題を計算して真だと確認する」ことを使っている。
-/
theorem deck_cardinality : Finset.card deck = 52 := by
  rfl
