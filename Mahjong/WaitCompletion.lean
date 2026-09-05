import Mahjong.Basic
import Mahjong.Pattern

/-!
# 待ちと和了分割

`WaitCompletion` は、1つの待ち牌と、その牌を加えたときの通常形の和了分割を表す。
牌列から `WaitCompletion` を見つける処理は `WaitCompletionFinder`、見つかった形の符号化は
`WaitDecompositionCode` が担当する。
-/

namespace WinningComponent

/--
完成分割内の部品に標準順を与えるための数値キー。

雀頭、順子、刻子には互いに重ならない数値範囲を割り当てる。それぞれの範囲内では、牌種、
スート、順子の開始位置からキーを決める。後続の `canonicalize` はこのキーの順に和了構成部品を並べる。
-/
def orderKey : WinningComponent → Nat
  | .inl (.toitsu tile) => tile.orderKey
  | .inr (.shuntsu (.shuntsu suit start)) =>
      Tile.count + suit.orderKey * shuntsuStartCount + start.val
  | .inr (.koutsu tile) => Tile.count + Suit.count * shuntsuStartCount + tile.orderKey

example : orderKey (WinningComponent.pair (.numbered .Manzu 4)) = 4 := rfl
example : orderKey (WinningComponent.shuntsu .Pinzu ⟨3, by decide⟩) = 44 := rfl
example : orderKey (WinningComponent.koutsu (.honor .East)) = 82 := rfl

/--
和了構成部品の標準順キーが等しければ、元の和了構成部品も等しい。

これは `orderKey` が雀頭、順子、刻子を同じ番号へ潰さず、各種類の内部でも異なる牌や順子を
区別することを保証する。したがって、後続処理は和了構成部品そのものではなく数値キーを使って整列しても、
部品を見分けるための情報を失わない。

`WinningComponent` は有限個しかないため、証明では `native_decide` がすべての組合せを計算してこの主張を確認する。

読むためのLean語彙: `Function.Injective`, `native_decide`。
-/
theorem orderKey_injective : Function.Injective orderKey := by
  native_decide

private def orderLE (a b : WinningComponent) : Bool :=
  decide (orderKey a ≤ orderKey b)

private theorem orderKeyLE_trans (a b c : WinningComponent) :
    orderLE a b = true → orderLE b c = true → orderLE a c = true := by
  simp [orderLE]
  intro first second
  omega

private theorem orderKeyLE_total (a b : WinningComponent) :
    (orderLE a b || orderLE b a) = true := by
  simp [orderLE, Nat.le_total]

/--
和了分割を表す `List WinningComponent` を、`orderKey` の昇順に並べた標準順表現へ変換する。

ここで同一視するのは、同じ和了構成部品を同じ個数だけ含み、リスト上の順番だけが異なる列である。
入力に含まれる和了構成部品とその個数は変えず、その同値な列から標準順の1列を選ぶ。

この関数単体の返り値は通常の `List WinningComponent` である。公開結果として保持するときは、
`CanonicalWinningComponents.ofList` で標準順の証拠付きの型へ包む。
-/
def canonicalize (winningComponents : List WinningComponent) : List WinningComponent :=
  winningComponents.mergeSort orderLE

example :
    canonicalize
        [WinningComponent.pair (.numbered .Manzu 4),
         WinningComponent.shuntsu .Pinzu ⟨3, by decide⟩] =
      canonicalize
        [WinningComponent.shuntsu .Pinzu ⟨3, by decide⟩,
         WinningComponent.pair (.numbered .Manzu 4)] := by
  native_decide

/--
同じ和了構成部品を同じ個数だけ含む2つの和了分割は、入力順によらず同じ標準順表現を持つ。

仮定 `first.Perm second` は、2つのリストで要素と重複数が同じであり、順番だけが異なり得ることを表す。
証明では、両方の `canonicalize` がキー順に整列済みであることと、元のリストから要素を増減していないことを
それぞれ示す。`orderKey_injective` により同じキーの異なる和了構成部品は存在しないため、整列後の2つのリストは
要素ごとに一致する。

この定理により、後続処理は和了分割を作った探索順ではなく、そこに含まれる和了構成部品と個数だけを比較できる。

読むためのLean語彙: `List.Perm`, `mergeSort`, `apply`, `intro`, `simpa`, `using`, `omega`, `.trans`, `.symm`, `exact`。
-/
theorem canonicalize_eq_of_perm {first second : List WinningComponent}
    (permutation : first.Perm second) :
    canonicalize first = canonicalize second := by
  apply List.Perm.eq_of_pairwise (le := fun a b => orderKey a ≤ orderKey b)
  · intro a b _ _ firstLe secondLe
    apply orderKey_injective
    omega
  · simpa [canonicalize, orderLE] using
      List.pairwise_mergeSort orderKeyLE_trans orderKeyLE_total first
  · simpa [canonicalize, orderLE] using
      List.pairwise_mergeSort orderKeyLE_trans orderKeyLE_total second
  · exact (List.mergeSort_perm _ _).trans
      (permutation.trans (List.mergeSort_perm _ _).symm)

/-- 標準化済みの列をもう一度標準化しても結果は変わらない。 -/
theorem canonicalize_idempotent (winningComponents : List WinningComponent) :
    canonicalize (canonicalize winningComponents) = canonicalize winningComponents := by
  apply canonicalize_eq_of_perm
  exact List.mergeSort_perm _ _

end WinningComponent

/-- 標準順へ正規化済みである証拠を持つ和了構成部品列。 -/
structure CanonicalWinningComponents where
  components : List WinningComponent
  canonical : components = WinningComponent.canonicalize components

namespace CanonicalWinningComponents

/-- 任意の和了構成部品列を標準順へ正規化し、証拠付きの値として包む。 -/
def ofList (components : List WinningComponent) : CanonicalWinningComponents :=
  { components := WinningComponent.canonicalize components
    canonical := (WinningComponent.canonicalize_idempotent components).symm }

/-- 証拠を忘れて、標準順の和了構成部品列を通常のリストとして取り出す。 -/
def toList (components : CanonicalWinningComponents) : List WinningComponent :=
  components.components

@[simp] theorem toList_ofList (components : List WinningComponent) :
    (ofList components).toList = WinningComponent.canonicalize components := rfl

theorem ext {first second : CanonicalWinningComponents}
    (componentsEq : first.components = second.components) : first = second := by
  cases first with
  | mk firstComponents firstCanonical =>
      cases second with
      | mk secondComponents secondCanonical =>
          simp at componentsEq
          subst secondComponents
          simp

theorem ofList_eq_of_perm {first second : List WinningComponent}
    (permutation : first.Perm second) :
    ofList first = ofList second := by
  apply ext
  exact WinningComponent.canonicalize_eq_of_perm permutation

instance : BEq CanonicalWinningComponents where
  beq first second := first.components == second.components

instance : DecidableEq CanonicalWinningComponents := fun first second =>
  if componentsEq : first.components = second.components then
    isTrue (ext componentsEq)
  else
    isFalse (fun equal => by
      apply componentsEq
      cases equal
      rfl)

instance : Repr CanonicalWinningComponents where
  reprPrec components prec := reprPrec components.components prec

end CanonicalWinningComponents

/-- 1つの待ち牌と、その牌を加えた和了形の標準順分割。 -/
structure WaitCompletion where
  wait : Tile
  winningComponents : CanonicalWinningComponents
deriving BEq, DecidableEq, Repr
