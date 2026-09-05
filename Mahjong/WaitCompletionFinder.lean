import Mahjong.WaitCompletion

/-!
# 待ちと和了分割の探索

`IsStandardAgari`、`IsWaitFor`、`IsTenpai` が通常形の意味論を定め、
`Wait tiles` が聴牌牌列 `tiles` に結び付いた待ちの証拠を表す。
`waitingTiles` は実際の待ち牌を計算する決定手続きであり、`findWaitCompletions` は、
待ち牌を加えた和了形をチャンクへ分解して得られる集合に対して正規化を行う。

このモジュールは物理牌ではなく、牌種 `Tile` のリストを対象にする。重複はリスト内の
出現回数で表す。`waitingTiles` は手牌枚数を1、4、7、10、13枚に限定し、
すべての牌種が4枚以下であることを確認してから探索する。
-/
namespace WaitCompletionFinder

/-- `available` から `wanted` の牌種列を多重集合的に取り除く。 -/
def removeTiles : List Tile → List Tile → Option (List Tile)
  | available, [] => some available
  | available, wanted :: rest =>
      if available.contains wanted then
        removeTiles (available.erase wanted) rest
      else
        none

/--
多重集合的な除去が `remaining` を返すことと、除去対象と残りを合わせた牌列が元の牌列の
順列であることは同値。これにより、`removeTiles` の成否が入力リストの並び順に依存しない。
-/
theorem exists_removeTiles_eq_some_iff_perm (available wanted remaining : List Tile) :
    (∃ output, removeTiles available wanted = some output ∧ output.Perm remaining) ↔
      (wanted ++ remaining).Perm available := by
  induction wanted generalizing available with
  | nil =>
      constructor
      · rintro ⟨output, removed, permutation⟩
        simp only [removeTiles, Option.some.injEq] at removed
        subst output
        exact permutation.symm
      · intro permutation
        exact ⟨available, rfl, permutation.symm⟩
  | cons tile wanted inductionHypothesis =>
      constructor
      · rintro ⟨output, removed, outputPerm⟩
        simp only [removeTiles] at removed
        split at removed
        · rename_i present
          have member : tile ∈ available := by simpa using present
          have tailPerm :=
            (inductionHypothesis (available.erase tile)).mp
              ⟨output, removed, outputPerm⟩
          exact (tailPerm.cons tile).trans (List.perm_cons_erase member).symm
        · simp at removed
      · intro permutation
        have member : tile ∈ available :=
          permutation.mem_iff.mp (by simp)
        have tailPerm : (wanted ++ remaining).Perm (available.erase tile) :=
          (permutation.trans (List.perm_cons_erase member)).cons_inv
        obtain ⟨output, removed, outputPerm⟩ :=
          (inductionHypothesis (available.erase tile)).mpr tailPerm
        refine ⟨output, ?_, outputPerm⟩
        simp only [removeTiles]
        rw [if_pos (by simpa using member)]
        exact removed

example :
    removeTiles
        [.numbered .Manzu 4, .numbered .Manzu 4, .numbered .Pinzu 0]
        [.numbered .Manzu 4] =
      some [.numbered .Manzu 4, .numbered .Pinzu 0] := by
  native_decide

/--
除去対象 `wanted` の後ろに残したい牌列 `remaining` を連結した入力から `wanted` を除くと、
`remaining` がそのまま返る。

`removeTiles` は同じ牌種を一度にすべて消すのではなく、`wanted` の各要素について最初の1枚だけを消す。
そのため `wanted` と `remaining` に同じ牌種が含まれていても、`remaining` 側の出現回数は保存される。

証明は `wanted` に対する帰納法で行う。空列なら何も除かず、先頭牌がある場合はその1枚を消した計算を
`simp` で進め、残りの除去が成功するという帰納法の仮定を使う。

読むためのLean語彙: `++`, `Option`, `induction`, `nil`, `cons`, `rfl`, `simp`。
-/
theorem removeTiles_append_left (wanted remaining : List Tile) :
    removeTiles (wanted ++ remaining) wanted = some remaining := by
  induction wanted with
  | nil => rfl
  | cons tile wanted inductionHypothesis =>
      simp [removeTiles, inductionHypothesis]

/-!
## 雀頭候補の列挙

`pairComponentCandidates` は、34種類すべての牌種を雀頭の和了構成部品へ変換した探索候補である。
`pair_mem_pairComponentCandidates` は任意の雀頭を取りこぼさないこと、
`pair_of_mem_pairComponentCandidates` は候補に雀頭以外が混ざらないことをそれぞれ保証する。
-/

/-- 雀頭候補として使う、全牌種の対子和了構成部品。 -/
def pairComponentCandidates : List WinningComponent :=
  Tile.all.map .pair

example : WinningComponent.pair (.honor .Red) ∈ pairComponentCandidates := by
  simp [pairComponentCandidates, Tile.all, Honor.all, WinningComponent.pair]

/--
任意の雀頭は `pairComponentCandidates` に含まれる。

これは雀頭候補列挙の完全性を保証する。証明では雀頭から牌種を取り出し、すべての牌種が
`Tile.all` に含まれるという `Tile.mem_all` を使って、その牌種を対子にした候補が存在することを示す。

読むためのLean語彙: `rcases`, `simp`, `∈`。
-/
theorem pair_mem_pairComponentCandidates (pair : Toitsu) :
    (Sum.inl pair : WinningComponent) ∈ pairComponentCandidates := by
  rcases pair with ⟨tile⟩
  simp [pairComponentCandidates, Tile.mem_all tile, WinningComponent.pair]

/--
`pairComponentCandidates` に含まれる和了構成部品は、必ず何らかの雀頭である。

これは雀頭候補列挙の健全性を保証し、順子や刻子が雀頭候補へ混ざらないことを示す。
証明ではリストの要素が `Tile.all.map .pair` のどの牌種から作られたかを取り出し、
その牌種の対子を求める雀頭として返す。

読むためのLean語彙: `∃`, `obtain`, `List.mem_map`, `exact`, `rfl`。
-/
theorem pair_of_mem_pairComponentCandidates {component : WinningComponent}
    (member : component ∈ pairComponentCandidates) :
    ∃ pair : Toitsu, component = .inl pair := by
  obtain ⟨tile, _, rfl⟩ := List.mem_map.mp member
  exact ⟨.toitsu tile, rfl⟩

/-!
## 完成面子候補の和了構成部品への持ち上げ

`mentsuComponentCandidates` は、列挙済みの全順子・刻子を、和了分割で使う和了構成部品へ変換した探索候補である。
`mentsu_mem_mentsuComponentCandidates` は任意の完成面子を取りこぼさないこと、
`mentsu_of_mem_mentsuComponentCandidates` は候補に雀頭が混ざらないことをそれぞれ保証する。
-/

/-- 全順子・刻子を、完成面子側の `WinningComponent` として包んだ候補列。 -/
def mentsuComponentCandidates : List WinningComponent :=
  (MentsuCandidate.candidates).map fun mentsu => (Sum.inr mentsu : WinningComponent)

/--
任意の完成面子候補を包んだ和了構成部品は `mentsuComponentCandidates` に含まれる。

これは完成面子側の候補列挙の完全性を保証する。先に `MentsuCandidate.mem_candidates` が
全順子・刻子を列挙できることを示しているため、その候補を直和の右側 `.inr` に包めばよい。

読むためのLean語彙: `List.mem_map`, `.mpr`, `_root_`, `exact`, `∈`, `rfl`。
-/
theorem mentsu_mem_mentsuComponentCandidates (mentsu : MentsuCandidate) :
    (Sum.inr mentsu : WinningComponent) ∈ mentsuComponentCandidates := by
  exact List.mem_map.mpr ⟨mentsu, _root_.MentsuCandidate.mem_candidates mentsu, rfl⟩

/--
`mentsuComponentCandidates` に含まれる和了構成部品は、必ず何らかの順子または刻子である。

これは完成面子側の候補列挙の健全性を保証し、雀頭が完成面子候補へ混ざらないことを示す。
証明では `map` 元の `MentsuCandidate` を取り出し、それを求める完成面子として返す。

読むためのLean語彙: `∃`, `obtain`, `List.mem_map`, `.mp`, `exact`, `rfl`。
-/
theorem mentsu_of_mem_mentsuComponentCandidates {component : WinningComponent}
    (member : component ∈ mentsuComponentCandidates) :
    ∃ mentsu : MentsuCandidate, component = .inr mentsu := by
  obtain ⟨mentsu, _, rfl⟩ := List.mem_map.mp member
  exact ⟨mentsu, rfl⟩

example : WinningComponent.koutsu (.honor .Red) ∈ mentsuComponentCandidates := by
  exact mentsu_mem_mentsuComponentCandidates (.koutsu (.honor .Red))

/-!
## 牌種列を指定個数の完成面子へ分解する

`decomposeMentsu fuel tiles` は、牌種列 `tiles` 全体をちょうど `fuel` 個の順子・刻子へ分解する方法を
すべて列挙する。ここで `fuel` は再帰回数の単なる上限ではなく、求める完成面子の個数である。

`fuel = 0` では牌が残っていない場合だけ、空の分解を1件返す。`fuel + 1` では
`mentsuComponentCandidates` から最初の完成面子を選び、`removeTiles` に成功した候補について、
残りをちょうど `fuel` 個へ再帰的に分解する。除去できない候補や、指定個数を選んだ後に牌が余る枝は捨てる。

結果は `List (List WinningComponent)` であり、外側のリストが異なる分解方法、内側のリストが
1つの分解を構成する完成面子列を表す。

読むためのLean語彙: `fuel`, `fuel + 1`, `List.flatten`, `map`, `match`, `[]`, `::`。
-/

/-- 牌種列全体を、ちょうど指定個数の順子・刻子へ分解する方法を列挙する。 -/
def decomposeMentsu : Nat → List Tile → List (List WinningComponent)
  | 0, tiles =>
      if tiles.isEmpty then [[]] else []
  | fuel + 1, tiles =>
      List.flatten (mentsuComponentCandidates.map fun mentsu =>
        match removeTiles tiles mentsu.tiles with
        | some remaining =>
            (decomposeMentsu fuel remaining).map fun winningComponents => mentsu :: winningComponents
        | none => [])

    example : decomposeMentsu 0 [] = [[]] := rfl
    example : decomposeMentsu 0 [.numbered .Manzu 0] = [] := rfl

/--
`decomposeMentsu` が `tiles` をちょうど `fuel` 個の完成面子へ分解する操作履歴。

3つの引数は順に、完成面子の個数、分解前の牌種列、分解後の完成面子列を表す。
値を計算して返す関数ではなく、この3者が正しい分解関係にあることの証拠を作る `Prop` である。

- `done`: 0個の完成面子で空の牌種列を空の完成面子列へ分解する。
- `next`: 候補に含まれる完成面子を1つ選び、その牌を除いた残りに対する分解証拠の前へ追加する。

各 `next` は、選んだ値が完成面子候補である証拠と、実際にその牌を除けた証拠を要求する。
そのため、候補でない雀頭や、入力に存在しない牌から分解証拠を作ることはできない。

外延的な正しさは `MentsuPartitionSpec` で表し、この型は列挙器との対応証明に使う。

読むためのLean語彙: 添字付きinductive family, `Prop`, constructor, 暗黙の引数, `.done`, `.next`。
-/
inductive MentsuPartition : Nat → List Tile → List WinningComponent → Prop
| done : MentsuPartition 0 [] []
| next {fuel tiles remaining rest} (mentsu : WinningComponent)
    (candidate : mentsu ∈ mentsuComponentCandidates)
    (remove : removeTiles tiles mentsu.tiles = some remaining)
    (tail : MentsuPartition fuel remaining rest) :
    MentsuPartition (fuel + 1) tiles (mentsu :: rest)

example :
    MentsuPartition 1
      [.honor .Red, .honor .Red, .honor .Red]
      [WinningComponent.koutsu (.honor .Red)] := by
  apply MentsuPartition.next (WinningComponent.koutsu (.honor .Red))
  · exact mentsu_mem_mentsuComponentCandidates (.koutsu (.honor .Red))
  · rfl
  · exact .done

/--
完成面子列が `decomposeMentsu` の列挙結果に含まれることと、同じ分解を表す
`MentsuPartition` の証拠を作れることは同値である。

左から右は列挙器の健全性を示す。`fuel` に対する帰納法で、列挙結果を最初に選んだ完成面子と
残りの分解へ分解し、候補所属、牌の除去結果、帰納法で得た残りの証拠から `MentsuPartition.next` を作る。

右から左は列挙器の完全性を示す。`MentsuPartition` の証拠から最初の完成面子、除去結果、
残りの分解証拠を取り出し、帰納法の仮定で残りを列挙結果へ戻して、`map` と `flatten` 内の該当する枝を示す。

`fuel = 0` では、実行器と操作履歴のどちらも、入力牌列と完成面子列がともに空の場合だけ成立する。
この定理により、後続の証明は実行器のリスト操作を直接追わず、`MentsuPartition` の構築規則を使って
列挙結果の意味を論じられる。

読むためのLean語彙: `↔`, 健全性と完全性, `induction ... generalizing`, `constructor`, `split`,
`List.mem_flatten`, `List.mem_map`, `.mp`, `.mpr`, `subst`, `rw`, `▸`, `rename_i`。
-/
theorem mem_decomposeMentsu_iff (fuel : Nat) (tiles : List Tile)
    (components : List WinningComponent) :
    components ∈ decomposeMentsu fuel tiles ↔ MentsuPartition fuel tiles components := by
  induction fuel generalizing tiles components with
  | zero =>
      constructor
      · intro member
        simp only [decomposeMentsu] at member
        split at member
        · have tilesEmpty : tiles = [] := List.isEmpty_iff.mp ‹tiles.isEmpty = true›
          subst tiles
          simp only [List.mem_singleton] at member
          subst components
          exact .done
        · simp at member
      · intro partition
        cases partition
        simp [decomposeMentsu]
  | succ fuel inductionHypothesis =>
      constructor
      · intro member
        simp only [decomposeMentsu] at member
        obtain ⟨generated, generatedMember, member⟩ := List.mem_flatten.mp member
        obtain ⟨mentsu, candidate, rfl⟩ := List.mem_map.mp generatedMember
        cases removeEq : removeTiles tiles mentsu.tiles with
        | none => simp [removeEq] at member
        | some remaining =>
          rw [removeEq] at member
          obtain ⟨rest, restMember, componentsEq⟩ := List.mem_map.mp member
          exact componentsEq ▸
            MentsuPartition.next mentsu candidate removeEq
              ((inductionHypothesis remaining rest).mp restMember)
      · intro partition
        cases partition with
        | next mentsu candidate remove tail =>
            rename_i remaining rest
            apply List.mem_flatten.mpr
            refine ⟨(decomposeMentsu fuel remaining).map fun tail => mentsu :: tail, ?_, ?_⟩
            · apply List.mem_map.mpr
              exact ⟨mentsu, candidate, by simp [remove]⟩
            · exact List.mem_map.mpr
                ⟨rest, (inductionHypothesis remaining rest).mpr tail, rfl⟩

example :
    [WinningComponent.koutsu (.honor .Red)] ∈
      decomposeMentsu 1 [.honor .Red, .honor .Red, .honor .Red] := by
  apply (mem_decomposeMentsu_iff 1
    [.honor .Red, .honor .Red, .honor .Red]
    [WinningComponent.koutsu (.honor .Red)]).mpr
  apply MentsuPartition.next (WinningComponent.koutsu (.honor .Red))
  · exact mentsu_mem_mentsuComponentCandidates (.koutsu (.honor .Red))
  · rfl
  · exact .done

/--
正しい面子分解の証拠は、同じ牌を同じ枚数だけ持つ任意の入力順へ移せる。

`tiles.Perm other` は、`other` が `tiles` の順番だけを変えた牌列であることを表す。結論では
完成面子列 `components` と面子数 `fuel` を変えず、入力牌列だけを `other` へ置き換える。
したがって、`MentsuPartition` が表す分解可能性は入力リストの並び順に依存しない。

証明は分解証拠に対する帰納法で行い、並べ替え後の入力 `other` は各段階で変わるため一般化する。
`done` では空列の順列も空列なので、再び `done` を作れる。`next` では、元の除去結果と入力間の順列を
`exists_removeTiles_eq_some_iff_perm` から取り出し、仮定の順列とつなぐ。同じ先頭面子を `other` から
除去できることと、その新しい残りが元の残りの順列であることが得られるので、帰納法の仮定で末尾の
分解証拠を移し、`next` を作り直す。

読むためのLean語彙: `List.Perm`, `induction ... generalizing`, `List.Perm.nil_eq`, `obtain`,
`.trans`, `.symm`, `subst`。
-/
theorem MentsuPartition.of_perm {fuel : Nat} {tiles other : List Tile}
    {components : List WinningComponent} (partition : MentsuPartition fuel tiles components)
    (permutation : tiles.Perm other) : MentsuPartition fuel other components := by
  induction partition generalizing other with
  | done =>
      have otherEmpty : other = [] := (List.Perm.nil_eq permutation).symm
      subst other
      exact .done
  | next mentsu candidate remove tail inductionHypothesis =>
      rename_i fuel tiles remaining rest
      have removedPerm : (mentsu.tiles ++ remaining).Perm tiles :=
        (exists_removeTiles_eq_some_iff_perm tiles mentsu.tiles remaining).mp
          ⟨remaining, remove, .refl remaining⟩
      obtain ⟨output, removeOther, outputPerm⟩ :=
        (exists_removeTiles_eq_some_iff_perm other mentsu.tiles remaining).mpr
          (removedPerm.trans permutation)
      exact .next mentsu candidate removeOther
        (inductionHypothesis outputPerm.symm)

example :
    MentsuPartition 1
      [.numbered .Manzu 2, .numbered .Manzu 0, .numbered .Manzu 1]
      [WinningComponent.shuntsu .Manzu ⟨0, by decide⟩] := by
  have ordered : MentsuPartition 1
      [.numbered .Manzu 0, .numbered .Manzu 1, .numbered .Manzu 2]
      [WinningComponent.shuntsu .Manzu ⟨0, by decide⟩] := by
    apply MentsuPartition.next (WinningComponent.shuntsu .Manzu ⟨0, by decide⟩)
    · exact mentsu_mem_mentsuComponentCandidates
        (.shuntsu (.shuntsu .Manzu ⟨0, by decide⟩))
    · rfl
    · exact .done
  apply ordered.of_perm
  decide

/--
面子分割の全和了構成部品を牌列へ戻すと、入力牌列と同じ牌種を同じ枚数だけ含む。

リストの順番は一致しなくてもよいため、結論は等号ではなく `List.Perm` で表す。これにより、
分解が入力牌を失ったり、余分な牌を追加したり、同じ牌種の枚数を変えたりしないことが分かる。

証明は分解証拠に対する帰納法で行う。`done` では空列同士の順列を返す。`next` では、
`exists_removeTiles_eq_some_iff_perm` から「先頭面子の牌と除去後の残り」が入力牌列の順列であることを得る。
帰納法の仮定が末尾の和了構成部品牌と残り牌の順列を保証するので、`List.Perm.append_left` で両側へ
先頭面子の牌を加え、`.trans` で2つの順列関係をつなぐ。

読むためのLean語彙: `List.flatMap`, `List.Perm`, `induction`, `List.Perm.append_left`, `.trans`。
-/
theorem MentsuPartition.tiles_perm {fuel : Nat} {tiles : List Tile}
    {components : List WinningComponent} (partition : MentsuPartition fuel tiles components) :
    (components.flatMap WinningComponent.tiles).Perm tiles := by
  induction partition with
  | done => exact .refl []
  | next mentsu candidate remove tail inductionHypothesis =>
      rename_i fuel tiles remaining rest
      have removedPerm : (mentsu.tiles ++ remaining).Perm tiles :=
        (exists_removeTiles_eq_some_iff_perm tiles mentsu.tiles remaining).mp
          ⟨remaining, remove, .refl remaining⟩
      exact (List.Perm.append_left mentsu.tiles inductionHypothesis).trans removedPerm

example
    (partition : MentsuPartition 2
      [.honor .Red, .numbered .Manzu 0, .honor .Red,
        .numbered .Manzu 1, .honor .Red, .numbered .Manzu 2]
      [WinningComponent.koutsu (.honor .Red), WinningComponent.shuntsu .Manzu ⟨0, by decide⟩]) :
    ([WinningComponent.koutsu (.honor .Red), WinningComponent.shuntsu .Manzu ⟨0, by decide⟩].flatMap
      WinningComponent.tiles).Perm
      [.honor .Red, .numbered .Manzu 0, .honor .Red,
        .numbered .Manzu 1, .honor .Red, .numbered .Manzu 2] := by
  exact partition.tiles_perm

/--
`MentsuPartition` の分解結果に現れるすべての和了構成部品は、`mentsuComponentCandidates` に含まれる。

これは、分解結果 `components` の各要素が順子または刻子の候補として選ばれたことを保証する。
`mentsu_of_mem_mentsuComponentCandidates` と合わせると、面子分解へ雀頭が混ざらないことが分かる。

証明は分解証拠に対する帰納法で行う。`done` の完成面子列は空なので主張は自明である。
`next` では、調べる要素が列の先頭なら構築時に保存された `candidate` を使い、末尾にあれば
残りの分解証拠に対する帰納法の仮定を使う。

読むためのLean語彙: `∀`, `induction`, `intro`, `List.mem_cons`, `rcases`, `rfl | restMember`。
-/
theorem MentsuPartition.all_mentsu {fuel : Nat} {tiles : List Tile}
    {components : List WinningComponent} (partition : MentsuPartition fuel tiles components) :
    ∀ component ∈ components, component ∈ mentsuComponentCandidates := by
  induction partition with
  | done => simp
  | next mentsu candidate remove tail inductionHypothesis =>
      intro component member
      rcases List.mem_cons.mp member with rfl | restMember
      · exact candidate
      · exact inductionHypothesis component restMember

/-- 完成面子候補を構成する牌は常に `mentsuTileCount` 枚である。 -/
theorem WinningComponent.tiles_length_of_mem_mentsuComponentCandidates
    {component : WinningComponent} (member : component ∈ mentsuComponentCandidates) :
    component.tiles.length = mentsuTileCount := by
  obtain ⟨candidate, rfl⟩ := mentsu_of_mem_mentsuComponentCandidates member
  cases candidate with
  | shuntsu pattern => cases pattern; rfl
  | koutsu tile => rfl

/-- 完成面子候補列を牌へ戻した列の長さは、部品数の `mentsuTileCount` 倍である。 -/
theorem WinningComponent.flatMap_tiles_length_of_all_mentsu
    (components : List WinningComponent)
    (allMentsu : ∀ component ∈ components, component ∈ mentsuComponentCandidates) :
    (components.flatMap WinningComponent.tiles).length = components.length * mentsuTileCount := by
  induction components with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      have firstLength := tiles_length_of_mem_mentsuComponentCandidates
        (allMentsu first (by simp))
      have restCandidates : ∀ component ∈ rest, component ∈ mentsuComponentCandidates := by
        intro component member
        exact allMentsu component (by simp [member])
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [firstLength, inductionHypothesis restCandidates]
      simp [Nat.add_mul, Nat.add_comm]

/-- 完成面子候補だけからなる部品列を、対応する `MentsuCandidate` の列として復元する。 -/
theorem exists_mentsuCandidates_of_all (components : List WinningComponent)
    (allMentsu : ∀ component ∈ components, component ∈ mentsuComponentCandidates) :
    ∃ candidates : List MentsuCandidate,
      components = candidates.map fun candidate => (Sum.inr candidate : WinningComponent) := by
  induction components with
  | nil => exact ⟨[], rfl⟩
  | cons first rest inductionHypothesis =>
      obtain ⟨candidate, rfl⟩ :=
        mentsu_of_mem_mentsuComponentCandidates (allMentsu first (by simp))
      have restCandidates :
          ∀ component ∈ rest, component ∈ mentsuComponentCandidates := by
        intro component member
        exact allMentsu component (by simp [member])
      obtain ⟨candidates, rfl⟩ := inductionHypothesis restCandidates
      exact ⟨candidate :: candidates, rfl⟩

example
    (partition : MentsuPartition 1
      [.honor .Red, .honor .Red, .honor .Red]
      [WinningComponent.koutsu (.honor .Red)]) :
    WinningComponent.koutsu (.honor .Red) ∈ mentsuComponentCandidates := by
  exact partition.all_mentsu _ (by simp)

    /--
    面子分割の和了構成部品列は、順子・刻子だけを持つ `MentsuCandidate` の列として復元できる。

    `all_mentsu` が各要素の候補所属を個別に保証するのに対し、この定理は列全体に対応する
    `candidates` を作り、各要素を直和の右側へ入れ直すと元の `components` に一致することを保証する。
    要素の順番と重複も `map` によってそのまま保存される。

    証明は分解証拠に対する帰納法で行う。`done` では空列を返す。`next` では、先頭の候補所属から
    `mentsu_of_mem_mentsuComponentCandidates` で具体的な `MentsuCandidate` を取り出し、帰納法で復元した
    末尾の列へ追加する。

    読むためのLean語彙: `∃`, `List.map`, `induction`, `obtain`, `rfl`, `⟨...⟩`。
    -/
    theorem MentsuPartition.exists_candidates {fuel : Nat} {tiles : List Tile}
      {components : List WinningComponent} (partition : MentsuPartition fuel tiles components) :
      ∃ candidates : List MentsuCandidate,
        components = candidates.map fun candidate => (Sum.inr candidate : WinningComponent) := by
      exact exists_mentsuCandidates_of_all components partition.all_mentsu

    example
        (partition : MentsuPartition 1
          [.honor .Red, .honor .Red, .honor .Red]
          [WinningComponent.koutsu (.honor .Red)]) :
        ∃ candidates : List MentsuCandidate,
          [WinningComponent.koutsu (.honor .Red)] =
            candidates.map fun candidate => (Sum.inr candidate : WinningComponent) := by
      exact partition.exists_candidates

  /--
  面子分割の `fuel` は、生成される完成面子列の長さに一致する。

  したがって `fuel` は探索回数の上限ではなく、この分解が含む完成面子の個数として読める。
  証明は分解証拠に対する帰納法で行う。`done` では両辺が `0` であり、`next` では
  完成面子列の長さと `fuel` がともに1増えるので、残りの分解に対する帰納法の仮定から従う。

  読むためのLean語彙: `List.length`, `induction`, `rfl`, `simp [inductionHypothesis]`。
  -/
  theorem MentsuPartition.components_length {fuel : Nat} {tiles : List Tile}
      {components : List WinningComponent} (partition : MentsuPartition fuel tiles components) :
      components.length = fuel := by
    induction partition with
    | done => rfl
    | next mentsu candidate remove tail inductionHypothesis =>
        simp [inductionHypothesis]

  example
      (partition : MentsuPartition 1
        [.honor .Red, .honor .Red, .honor .Red]
        [WinningComponent.koutsu (.honor .Red)]) :
      [WinningComponent.koutsu (.honor .Red)].length = 1 := by
    exact partition.components_length

/--
完成面子候補だけからなる部品列を牌列へ平坦化すると、その部品列自身へ正しく分解できる。

入力牌列 `components.flatMap WinningComponent.tiles` は、各部品を構成する牌を部品の順番どおりに連結した列である。
この定理はその列について `MentsuPartition` の証拠を構築する。入力牌列の任意の並び替えまでを
ここで扱うのではなく、その場合は `MentsuPartition.of_perm` と組み合わせる。

証明は `components` に対する帰納法で行う。空列は `MentsuPartition.done` で分解できる。
先頭 `first` がある場合は、`allMentsu` から先頭と末尾の候補所属をそれぞれ取り出し、帰納法で
末尾の分解証拠を作る。連結した牌列から先頭部品の牌を除く計算は `removeTiles_append_left` が保証するため、
これらを `MentsuPartition.next` へ渡せばよい。

読むためのLean語彙: `List.flatMap`, `∀`, `induction`, `have`, `simp`, `.done`, `.next`。
-/
theorem mentsuPartition_flatMap (components : List WinningComponent)
    (allMentsu : ∀ component ∈ components, component ∈ mentsuComponentCandidates) :
    MentsuPartition components.length (components.flatMap WinningComponent.tiles) components := by
  induction components with
  | nil => exact .done
  | cons first rest inductionHypothesis =>
      have firstCandidate := allMentsu first (by simp)
      have restCandidates : ∀ component ∈ rest, component ∈ mentsuComponentCandidates := by
        intro component member
        exact allMentsu component (by simp [member])
      have tail := inductionHypothesis restCandidates
      have removeFirst :
          removeTiles (first.tiles ++ rest.flatMap WinningComponent.tiles) first.tiles =
            some (rest.flatMap WinningComponent.tiles) := by
        exact removeTiles_append_left _ _
      exact .next first firstCandidate removeFirst tail

/-- 面子分割の、除去順に依存しない公開仕様。 -/
structure MentsuPartitionSpec (fuel : Nat) (tiles : List Tile)
    (components : List WinningComponent) : Prop where
  components_length : components.length = fuel
  all_mentsu : ∀ component ∈ components, component ∈ mentsuComponentCandidates
  tiles_perm : (components.flatMap WinningComponent.tiles).Perm tiles

/--
`MentsuPartition` を、操作履歴に依存しない3つの条件で特徴づける。

分解証拠が存在することは、部品数が `fuel` に一致し、すべての部品が完成面子候補であり、
部品を牌へ戻した列が入力牌列の順列であることと同値である。右から左では、まず部品を並べた
順序の入力に対する分解証拠を `mentsuPartition_flatMap` で作り、`of_perm` で実際の入力順へ移す。
-/
theorem MentsuPartition.iff_extensional {fuel : Nat} {tiles : List Tile}
    {components : List WinningComponent} :
    MentsuPartition fuel tiles components ↔ MentsuPartitionSpec fuel tiles components := by
  constructor
  · intro partition
    exact ⟨partition.components_length, partition.all_mentsu, partition.tiles_perm⟩
  · intro specification
    have partition :=
      (mentsuPartition_flatMap components specification.all_mentsu).of_perm
        specification.tiles_perm
    exact specification.components_length ▸ partition

/-- `decomposeMentsu` の列挙所属を、操作履歴を介さず外延仕様として読む。 -/
theorem mem_decomposeMentsu_iff_spec (fuel : Nat) (tiles : List Tile)
    (components : List WinningComponent) :
    components ∈ decomposeMentsu fuel tiles ↔ MentsuPartitionSpec fuel tiles components :=
  (mem_decomposeMentsu_iff fuel tiles components).trans MentsuPartition.iff_extensional

example :
    MentsuPartition 1
      [.honor .Red, .honor .Red, .honor .Red]
      [WinningComponent.koutsu (.honor .Red)] := by
  have partition := mentsuPartition_flatMap [WinningComponent.koutsu (.honor .Red)] (by
    intro component member
    simp only [List.mem_singleton] at member
    subst component
    exact mentsu_mem_mentsuComponentCandidates (.koutsu (.honor .Red)))
  simpa [WinningComponent.koutsu, WinningComponent.tiles, MentsuCandidate.tiles] using partition

/-- 牌種リストを雀頭1つと完成面子列に分解する。 -/
def winningPartitions (tiles : List Tile) : List (List WinningComponent) :=
  List.flatten (pairComponentCandidates.map fun pairComponent =>
    match removeTiles tiles pairComponent.tiles with
    | some remaining =>
        (decomposeMentsu (remaining.length / mentsuTileCount) remaining).map fun winningComponents =>
          pairComponent :: winningComponents
    | none => [])

/-- `winningPartitions` が雀頭を除き、残りを完成面子へ分解する操作履歴。 -/
inductive WinningPartition (tiles : List Tile) : List WinningComponent → Prop
| intro {remaining rest} (pair : WinningComponent)
    (pairCandidate : pair ∈ pairComponentCandidates)
    (removePair : removeTiles tiles pair.tiles = some remaining)
    (mentsuPartition : MentsuPartition (remaining.length / mentsuTileCount) remaining rest) :
    WinningPartition tiles (pair :: rest)

/--
`winningPartitions` が列挙する和了構成部品列と、`WinningPartition` の証拠を作れる和了構成部品列は一致する。

左辺は実行可能な探索結果への所属、右辺は同じ除去手順を記録した操作履歴を表す。
外延的な公開仕様との対応は `mem_winningPartitions_iff_spec` が与える。

健全性方向では、外側の `flatten` と雀頭候補の `map` から、実際に選ばれた雀頭を取り出す。
雀頭の除去が成功した枝では、内側の `map` から残りの完成面子列を取り出し、
`mem_decomposeMentsu_iff` の健全性方向で `MentsuPartition` の証拠へ変換して `WinningPartition.intro` を作る。

完全性方向では `WinningPartition.intro` に保存された雀頭、除去結果、面子分解証拠を取り出す。
`mem_decomposeMentsu_iff` の完全性方向で残りの分解を実行器の結果へ戻し、対応する雀頭候補の
`map` の枝と、その中の完成面子列の `map` への所属を順に組み立てる。

読むためのLean語彙: `↔`, 健全性と完全性, `List.mem_flatten`, `List.mem_map`, `obtain`,
`cases`, `.mp`, `.mpr`, `▸`, `refine`, `?_`。
-/
theorem mem_winningPartitions_iff (tiles : List Tile) (components : List WinningComponent) :
    components ∈ winningPartitions tiles ↔ WinningPartition tiles components := by
  constructor
  · intro member
    simp only [winningPartitions] at member
    obtain ⟨generated, generatedMember, member⟩ := List.mem_flatten.mp member
    obtain ⟨pair, pairCandidate, rfl⟩ := List.mem_map.mp generatedMember
    cases removeEq : removeTiles tiles pair.tiles with
    | none => simp [removeEq] at member
    | some remaining =>
      rw [removeEq] at member
      obtain ⟨rest, restMember, componentsEq⟩ := List.mem_map.mp member
      exact componentsEq ▸
        WinningPartition.intro pair pairCandidate removeEq
          ((mem_decomposeMentsu_iff _ _ _).mp restMember)
  · intro partition
    cases partition with
    | intro pair pairCandidate removePair partition =>
        rename_i remaining rest
        apply List.mem_flatten.mpr
        refine ⟨(decomposeMentsu (remaining.length / mentsuTileCount) remaining).map
          fun components => pair :: components, ?_, ?_⟩
        · apply List.mem_map.mpr
          exact ⟨pair, pairCandidate, by simp [removePair]⟩
        · exact List.mem_map.mpr
            ⟨rest, (mem_decomposeMentsu_iff _ _ _).mpr partition, rfl⟩

example :
    [WinningComponent.pair (.numbered .Manzu 4),
      WinningComponent.shuntsu .Manzu ⟨0, by decide⟩] ∈
      winningPartitions
        [.numbered .Manzu 4, .numbered .Manzu 4, .numbered .Manzu 0,
          .numbered .Manzu 1, .numbered .Manzu 2] := by
  apply (mem_winningPartitions_iff _ _).mpr
  apply WinningPartition.intro
    (remaining := [.numbered .Manzu 0, .numbered .Manzu 1, .numbered .Manzu 2])
    (WinningComponent.pair (.numbered .Manzu 4))
  · exact pair_mem_pairComponentCandidates (.toitsu (.numbered .Manzu 4))
  · rfl
  · change MentsuPartition 1
      [.numbered .Manzu 0, .numbered .Manzu 1, .numbered .Manzu 2]
      [WinningComponent.shuntsu .Manzu ⟨0, by decide⟩]
    apply MentsuPartition.next (WinningComponent.shuntsu .Manzu ⟨0, by decide⟩)
    · exact mentsu_mem_mentsuComponentCandidates
        (.shuntsu (.shuntsu .Manzu ⟨0, by decide⟩))
    · rfl
    · exact .done

/-- 通常和了分割の、除去順に依存しない公開仕様。 -/
def WinningPartitionSpec (tiles : List Tile) (components : List WinningComponent) : Prop :=
  ∃ pair rest,
    components = pair :: rest ∧
    pair ∈ pairComponentCandidates ∧
    (∀ component ∈ rest, component ∈ mentsuComponentCandidates) ∧
    (components.flatMap WinningComponent.tiles).Perm tiles

/--
`WinningPartition` を、除去順に依存しない雀頭、完成面子列、牌の保存条件で特徴づける。

先頭部品が雀頭候補、残りがすべて完成面子候補であり、全部品を牌へ戻した列が入力牌列の
順列なら、実際の雀頭除去後の並びに対して `MentsuPartition.iff_extensional` を適用できる。
-/
theorem WinningPartition.iff_extensional {tiles : List Tile}
    {components : List WinningComponent} :
    WinningPartition tiles components ↔ WinningPartitionSpec tiles components := by
  unfold WinningPartitionSpec
  constructor
  · intro partition
    cases partition with
    | intro pair pairCandidate removePair mentsuPartition =>
        rename_i remaining rest
        have removedPerm : (pair.tiles ++ remaining).Perm tiles :=
          (exists_removeTiles_eq_some_iff_perm tiles pair.tiles remaining).mp
            ⟨remaining, removePair, .refl remaining⟩
        have tilesPerm :=
          (List.Perm.append_left pair.tiles mentsuPartition.tiles_perm).trans removedPerm
        exact ⟨pair, rest, rfl, pairCandidate, mentsuPartition.all_mentsu, tilesPerm⟩
  · rintro ⟨pair, rest, rfl, pairCandidate, allMentsu, permutation⟩
    let remaining := rest.flatMap WinningComponent.tiles
    have removedPerm : (pair.tiles ++ remaining).Perm tiles := by
      simpa [remaining] using permutation
    obtain ⟨output, removePair, outputPerm⟩ :=
      (exists_removeTiles_eq_some_iff_perm tiles pair.tiles remaining).mpr removedPerm
    have remainingLength : remaining.length = rest.length * mentsuTileCount := by
      exact WinningComponent.flatMap_tiles_length_of_all_mentsu rest allMentsu
    have outputLength : output.length = rest.length * mentsuTileCount :=
      outputPerm.length_eq.trans remainingLength
    have fuelEq : rest.length = output.length / mentsuTileCount := by
      rw [outputLength]
      simp [mentsuTileCount]
    apply WinningPartition.intro pair pairCandidate removePair
    apply MentsuPartition.iff_extensional.mpr
    exact ⟨fuelEq, allMentsu, outputPerm.symm⟩

/-- `winningPartitions` の列挙所属を、操作履歴を介さず外延仕様として読む。 -/
theorem mem_winningPartitions_iff_spec (tiles : List Tile)
    (components : List WinningComponent) :
    components ∈ winningPartitions tiles ↔ WinningPartitionSpec tiles components :=
  (mem_winningPartitions_iff tiles components).trans WinningPartition.iff_extensional

/-- 外延的な通常和了分割仕様を、同じ牌の別の入力順へ移す。 -/
theorem WinningPartitionSpec.of_perm {tiles other : List Tile}
    {components : List WinningComponent} (specification : WinningPartitionSpec tiles components)
    (permutation : tiles.Perm other) : WinningPartitionSpec other components := by
  unfold WinningPartitionSpec at specification ⊢
  obtain ⟨pair, rest, componentsEq, pairCandidate, allMentsu, tilesPerm⟩ := specification
  exact ⟨pair, rest, componentsEq, pairCandidate, allMentsu, tilesPerm.trans permutation⟩

/--
正しい通常和了分割の証拠は、同じ牌を同じ枚数だけ持つ任意の入力順へ移せる。

`tiles.Perm other` は入力牌列の順番だけが異なることを表す。結論では雀頭と完成面子列 `components` を
変えず、入力だけを `other` へ置き換えるため、通常和了としての分割可能性が入力順に依存しないと分かる。

証明は操作履歴を `WinningPartitionSpec` へ変換し、外延的な牌の順列を `other` まで推移させた後、
再び操作履歴へ戻す。除去後リストや `fuel` 添字をこの境界で扱う必要はない。

読むためのLean語彙: `List.Perm`, `.trans`, `.mp`, `.mpr`。
-/
theorem WinningPartition.of_perm {tiles other : List Tile} {components : List WinningComponent}
    (partition : WinningPartition tiles components) (permutation : tiles.Perm other) :
    WinningPartition other components := by
  exact WinningPartition.iff_extensional.mpr
    ((WinningPartition.iff_extensional.mp partition).of_perm permutation)

example
    (partition : WinningPartition
      [.numbered .Manzu 4, .numbered .Manzu 4, .numbered .Manzu 0,
        .numbered .Manzu 1, .numbered .Manzu 2]
      [WinningComponent.pair (.numbered .Manzu 4),
        WinningComponent.shuntsu .Manzu ⟨0, by decide⟩]) :
    WinningPartition
      [.numbered .Manzu 2, .numbered .Manzu 4, .numbered .Manzu 0,
        .numbered .Manzu 4, .numbered .Manzu 1]
      [WinningComponent.pair (.numbered .Manzu 4),
        WinningComponent.shuntsu .Manzu ⟨0, by decide⟩] := by
  exact partition.of_perm (by decide)

/--
通常和了分割の全和了構成部品を牌列へ戻すと、入力牌列と同じ牌種を同じ枚数だけ含む。

`WinningPartition` は先頭に雀頭を1つ持ち、その後ろに `MentsuPartition` が保証する完成面子列を持つ。
この定理は、雀頭を含む分割全体について牌の欠落、追加、重複数の変化がないことを `List.Perm` で表す。

証明では分割証拠を `cases` で唯一の構築規則 `intro` へ分解する。雀頭の除去結果から
`exists_removeTiles_eq_some_iff_perm` を使い、「雀頭の牌と残り牌」が入力牌列の順列であることを得る。
残りの完成面子を牌へ戻した列と残り牌の順列は `mentsuPartition.tiles_perm` が保証する。
その両側へ雀頭の牌を `List.Perm.append_left` で加え、`.trans` で入力牌列までつなぐ。

読むためのLean語彙: `cases`, `List.flatMap`, `List.Perm`, `List.Perm.append_left`, `.trans`。
-/
theorem WinningPartition.tiles_perm {tiles : List Tile} {components : List WinningComponent}
    (partition : WinningPartition tiles components) :
    (components.flatMap WinningComponent.tiles).Perm tiles := by
  obtain ⟨_, _, _, _, _, permutation⟩ := WinningPartition.iff_extensional.mp partition
  exact permutation

example
    (partition : WinningPartition
      [.numbered .Manzu 4, .numbered .Manzu 0, .numbered .Manzu 4,
        .numbered .Manzu 1, .numbered .Manzu 2]
      [WinningComponent.pair (.numbered .Manzu 4),
        WinningComponent.shuntsu .Manzu ⟨0, by decide⟩]) :
    ([WinningComponent.pair (.numbered .Manzu 4),
      WinningComponent.shuntsu .Manzu ⟨0, by decide⟩].flatMap WinningComponent.tiles).Perm
      [.numbered .Manzu 4, .numbered .Manzu 0, .numbered .Manzu 4,
        .numbered .Manzu 1, .numbered .Manzu 2] := by
  exact partition.tiles_perm

/-- 牌種リストが通常形の和了形として分解できるか。 -/
def isWinning (tiles : List Tile) : Bool :=
  !(winningPartitions tiles).isEmpty

/-- 通常形聴牌として扱う手牌枚数。 -/
def IsTenpaiHandSize (size : Nat) : Prop :=
  size = 1 ∨ size = 4 ∨ size = 7 ∨ size = 10 ∨ size = 13

/-- 各牌種が物理的な上限枚数を超えていないこと。 -/
def HasLegalTileCounts (tiles : List Tile) : Prop :=
  ∀ tile, tiles.count tile ≤ copiesPerTile

/-- 待ち判定へ渡せる牌種列であること。 -/
def IsLegalTenpaiHand (tiles : List Tile) : Prop :=
  IsTenpaiHandSize tiles.length ∧ HasLegalTileCounts tiles

instance (size : Nat) : Decidable (IsTenpaiHandSize size) := by
  unfold IsTenpaiHandSize
  infer_instance

instance (tiles : List Tile) : Decidable (HasLegalTileCounts tiles) :=
  Fintype.decidableForallFintype

instance (tiles : List Tile) : Decidable (IsLegalTenpaiHand tiles) := by
  unfold IsLegalTenpaiHand
  infer_instance

/-- 牌種列が通常形（雀頭1つと完成面子列）の和了形であること。 -/
def IsStandardAgari (tiles : List Tile) : Prop :=
  isWinning tiles = true

/-- 有効な聴牌手に `candidate` を1枚加えると通常形で和了し、5枚目にもならないこと。 -/
def IsWaitFor (tiles : List Tile) (candidate : Tile) : Prop :=
  IsLegalTenpaiHand tiles ∧
    tiles.count candidate < copiesPerTile ∧
    IsStandardAgari (candidate :: tiles)

/--
同じ牌種を同じ枚数だけ含む牌姿へ並べ替えても、候補牌 `candidate` が通常形待ちであることは変わらない。

`IsWaitFor` の3条件のうち、合法な手牌枚数は `permutation.length_eq`、各牌種の合法枚数と候補牌を
もう1枚使えることは `permutation.count` で新しい入力へ移す。加牌後の和了条件はBool値を直接移さず、
`winningPartitions` が空でないことから分割を1つ取り出し、`mem_winningPartitions_iff` で
`WinningPartition` の証拠へ変換する。その証拠を `WinningPartition.of_perm` で並べ替え後へ移し、
対応する分割が列挙されることから再び `IsStandardAgari` を得る。

したがって待ちの意味は、牌姿リストの入力順ではなく、各牌種が何枚あるかだけで決まる。

読むためのLean語彙: `List.Perm`, `rcases`, `List.Perm.length_eq`, `List.Perm.count`,
`List.isEmpty_iff`, `obtain`, `.mp`, `.mpr`, `List.Perm.cons`。
-/
theorem IsWaitFor.of_perm {tiles other : List Tile} {candidate : Tile}
    (waitFor : IsWaitFor tiles candidate) (permutation : tiles.Perm other) :
    IsWaitFor other candidate := by
  rcases waitFor with ⟨⟨size, legal⟩, available, winning⟩
  constructor
  · constructor
    · simpa [permutation.length_eq] using size
    · intro tile
      simpa [permutation.count tile] using legal tile
  · constructor
    · simpa [permutation.count candidate] using available
    · unfold IsStandardAgari isWinning at winning ⊢
      have nonempty : winningPartitions (candidate :: tiles) ≠ [] := by
        simpa [List.isEmpty_iff] using winning
      obtain ⟨components, componentsMember⟩ := List.exists_mem_of_ne_nil _ nonempty
      have partition := (mem_winningPartitions_iff _ _).mp componentsMember
      have otherMember := (mem_winningPartitions_iff _ _).mpr
        (partition.of_perm (permutation.cons candidate))
      have otherNonempty : winningPartitions (candidate :: other) ≠ [] :=
        List.ne_nil_of_mem otherMember
      simp [otherNonempty]

example : IsWaitFor
    [.honor .Red, .honor .East, .honor .East, .honor .East] (.honor .Red) := by
  have original : IsWaitFor
      [.honor .East, .honor .East, .honor .East, .honor .Red] (.honor .Red) := by
    unfold IsWaitFor IsStandardAgari
    native_decide
  apply original.of_perm
  native_decide

/-- 牌種列が少なくとも1種類の通常形待ちを持つこと。 -/
def IsTenpai (tiles : List Tile) : Prop :=
  ∃ candidate, IsWaitFor tiles candidate

/-- 手牌に結び付いた通常形待ちの証拠。 -/
structure Wait (tiles : List Tile) where
  tile : Tile
  valid : IsWaitFor tiles tile

/-- 与えられた聴牌形に対し、加えると通常形で和了になる牌種を列挙する。 -/
def waitingTiles (tiles : List Tile) : List Tile :=
  if IsLegalTenpaiHand tiles then
    Tile.all.filter fun candidate =>
      (tiles.count candidate < copiesPerTile) && isWinning (candidate :: tiles)
  else
    []

/--
`waitingTiles` に候補牌が含まれることと、その牌が宣言的な通常形待ち `IsWaitFor` を満たすことは同値である。

左辺は実行可能な待ち牌列挙への所属、右辺は「手牌枚数と各牌種の枚数が合法」「候補牌が4枚未満」
「候補牌を加えると通常形で和了する」という仕様を表す。したがって、左から右は列挙の健全性、
右から左は完全性を保証する。

証明は手牌が `IsLegalTenpaiHand` を満たすかで場合分けする。合法な場合、`waitingTiles` の `filter` への
所属を展開すると、候補牌が `Tile.all` に含まれること、4枚未満であること、加牌後に和了することが得られる。
全牌種が `Tile.all` に含まれることを `Tile.mem_all` で消去し、Boolの論理積を `Bool.and_eq_true` で
命題の論理積へ直すと、`IsWaitFor` の定義と一致する。非合法な場合は `waitingTiles` が空列になり、
`IsWaitFor` の最初の条件も偽なので、両辺とも成立しない。

読むためのLean語彙: `↔`, 健全性と完全性, `by_cases`, `List.filter`, `simp`, `Bool.and_eq_true`。
-/
theorem mem_waitingTiles_iff (tiles : List Tile) (candidate : Tile) :
    candidate ∈ waitingTiles tiles ↔ IsWaitFor tiles candidate := by
  by_cases legal : IsLegalTenpaiHand tiles
  · simp [waitingTiles, legal, Tile.mem_all, IsWaitFor, IsStandardAgari,
      Bool.and_eq_true]
  · simp [waitingTiles, legal, IsWaitFor]

example : .honor .Red ∈ waitingTiles [.honor .Red] := by
  apply (mem_waitingTiles_iff _ _).mpr
  unfold IsWaitFor IsStandardAgari
  native_decide

/--
`waitingTiles` が少なくとも1種類の牌を返すことと、意味論上の通常形聴牌 `IsTenpai` は同値である。

左辺は列挙器を実行して確認できる条件、右辺は `IsWaitFor` を満たす牌種が存在するという宣言的な条件である。
したがってこの定理により、`waitingTiles tiles ≠ []` を通常形聴牌の決定手続きとして利用できる。

左から右へは、空でない列から要素 `candidate` を1つ取り出し、`mem_waitingTiles_iff` の健全性方向で
`IsWaitFor tiles candidate` を得る。右から左へは、仕様が与える待ち牌を同定理の完全性方向で列挙結果へ戻す。
列挙結果が空だと仮定すれば、その所属証拠と矛盾する。

読むためのLean語彙: `≠`, `∃`, `constructor`, `obtain`, `rintro`, `simp`。
-/
theorem waitingTiles_ne_nil_iff (tiles : List Tile) :
    waitingTiles tiles ≠ [] ↔ IsTenpai tiles := by
  constructor
  · intro nonempty
    obtain ⟨candidate, member⟩ := List.exists_mem_of_ne_nil _ nonempty
    exact ⟨candidate, (mem_waitingTiles_iff tiles candidate).mp member⟩
  · rintro ⟨candidate, valid⟩ empty
    have member := (mem_waitingTiles_iff tiles candidate).mpr valid
    simp [empty] at member

example : IsTenpai [.honor .Red] := by
  apply (waitingTiles_ne_nil_iff _).mp
  exact List.ne_nil_of_mem (a := .honor .Red) (by native_decide)

/--
待ち牌と、その待ち牌を加えた和了形の正規化済み分割を列挙する。

`winningPartitions` は完成面子を除去した順序も列として保持するため、同じ面子集合でも除去順が異なれば
複数の候補を生成する。`CanonicalWinningComponents.ofList` で部品順を標準化した後の `dedup` は、
同じ待ち牌と同じ標準分割になった候補だけを1件にまとめる。異なる待ち牌や異なる標準分割は保持する。
-/
def findWaitCompletions (tiles : List Tile) : List WaitCompletion :=
  let candidates : List WaitCompletion := do
    let wait ← waitingTiles tiles
    let winningComponents ← winningPartitions (wait :: tiles)
    pure { wait, winningComponents := CanonicalWinningComponents.ofList winningComponents }
  candidates.dedup

/--
`completion` が牌姿 `tiles` の待ちと和了分割を表すことの宣言的仕様。

証拠は待ち牌 `wait` と正規化前の分割 `rawComponents` を持ち、`wait` が `IsWaitFor tiles wait` を満たすこと、
加牌後の牌列が `rawComponents` へ通常和了分割できることを要求する。Finder が外部へ返す分割は
`WinningComponent.canonicalize rawComponents` なので、探索順の異なる同じ分割を同じ `WaitCompletion` として扱える。

読むためのLean語彙: 添字付き帰納型, `structure`, `WinningComponent.canonicalize`。
-/
inductive CompletionFor (tiles : List Tile) : WaitCompletion → Prop
| intro (wait : Tile) (rawComponents : List WinningComponent)
    (waitFor : IsWaitFor tiles wait)
  (partition : WinningPartitionSpec (wait :: tiles) rawComponents) :
    CompletionFor tiles
  { wait, winningComponents := CanonicalWinningComponents.ofList rawComponents }

/--
同じ牌種を同じ枚数だけ含む牌姿へ並べ替えても、`CompletionFor` の証拠をそのまま移せる。

`completion` に記録された待ち牌と正規化済み和了分割は変更しない。証拠を構成する
`IsWaitFor` は `IsWaitFor.of_perm` で新しい入力へ移し、加牌後の `WinningPartitionSpec` は、入力間の順列の
両側へ同じ待ち牌を加えた `permutation.cons wait` を `WinningPartitionSpec.of_perm` に渡して移す。
したがって `CompletionFor` の意味は、牌姿リストの偶然の入力順ではなく、牌種とその枚数だけで決まる。

読むためのLean語彙: `List.Perm`, `cases ... with`, `List.Perm.cons`, `exact`。
-/
theorem CompletionFor.of_perm {tiles other : List Tile} {completion : WaitCompletion}
    (valid : CompletionFor tiles completion) (permutation : tiles.Perm other) :
    CompletionFor other completion := by
  cases valid with
  | intro wait rawComponents waitFor partition =>
      exact .intro wait rawComponents (waitFor.of_perm permutation)
        (partition.of_perm (permutation.cons wait))

example {completion : WaitCompletion}
    (valid : CompletionFor
      [.honor .Red, .honor .East, .honor .East, .honor .East] completion) :
    CompletionFor
      [.honor .East, .honor .Red, .honor .East, .honor .East] completion := by
  apply valid.of_perm
  native_decide

/--
`findWaitCompletions` に結果が含まれることと、宣言的仕様 `CompletionFor` を満たすことは同値である。

左辺は実行可能なFinderへの所属、右辺は正しい待ち牌と通常和了分割が存在することを表す。したがって、
左から右はFinderが不正な組を返さないという健全性、右から左は正しい組を取りこぼさないという完全性を保証する。

証明では、まず `List.mem_dedup` により、重複除去の前後で所属が変わらないことを使う。健全性方向では
`List.bind_eq_flatMap` と `List.mem_flatMap` から、結果を生成した待ち牌と正規化前の分割を取り出す。
それぞれの所属証拠を `mem_waitingTiles_iff` と `mem_winningPartitions_iff_spec` で宣言的仕様へ変換すれば、
`CompletionFor` の構築に必要な2条件が揃う。完全性方向では同じ変換を逆向きに使い、仕様が持つ待ち牌と
分割を `do` 記法による列挙の所属証拠へ戻す。

読むためのLean語彙: `↔`, 健全性と完全性, `rw`, `List.mem_dedup`, `List.bind_eq_flatMap`,
`List.mem_flatMap`, `obtain`, `cases`, `refine`。
-/
theorem mem_findWaitCompletions_iff (tiles : List Tile) (completion : WaitCompletion) :
    completion ∈ findWaitCompletions tiles ↔ CompletionFor tiles completion := by
  rw [findWaitCompletions, List.mem_dedup]
  simp only [List.bind_eq_flatMap]
  constructor
  · intro member
    obtain ⟨wait, waitMember, completionMember⟩ := List.mem_flatMap.mp member
    obtain ⟨rawComponents, partitionMember, completionMember⟩ :=
      List.mem_flatMap.mp completionMember
    have completionEq : completion =
        { wait, winningComponents := CanonicalWinningComponents.ofList rawComponents } := by
      simpa using completionMember
    rw [completionEq]
    exact .intro wait rawComponents ((mem_waitingTiles_iff tiles wait).mp waitMember)
      ((mem_winningPartitions_iff_spec _ _).mp partitionMember)
  · intro valid
    cases valid with
    | intro wait rawComponents waitFor partition =>
        apply List.mem_flatMap.mpr
        refine ⟨wait, (mem_waitingTiles_iff tiles wait).mpr waitFor, ?_⟩
        apply List.mem_flatMap.mpr
        refine ⟨rawComponents, (mem_winningPartitions_iff_spec _ _).mpr partition, ?_⟩
        simp

example : CompletionFor [.honor .Red]
    { wait := .honor .Red
      winningComponents := CanonicalWinningComponents.ofList [WinningComponent.pair (.honor .Red)] } := by
  apply (mem_findWaitCompletions_iff _ _).mp
  have output : findWaitCompletions [.honor .Red] =
      [{ wait := .honor .Red
         winningComponents := CanonicalWinningComponents.ofList [WinningComponent.pair (.honor .Red)] }] := by
    native_decide
  simp [output]

/-!
## 分解に関する既約性

`waitCompletionCount` は待ち牌と和了形の組を数える。メンツを1つ除いた
聴牌形が同じ個数の分解を持つなら、その手牌はメンツ除去により可約である。
待ちでない牌列を既約とは扱わない。

これは分解数だけを比較する旧来の近似である。分類で使う根源的な既約性は
`WaitDecompositionCode.CanReduceMentsuPreservingWaitCores` が待ち核集合を比較する。
-/
def waitCompletionCount (tiles : List Tile) : Nat :=
  (findWaitCompletions tiles).length

/--
宣言的な通常形聴牌 `IsTenpai tiles` が成り立つかを、Leanが計算で判定できるようにする。

`IsTenpai` は待ち牌の存在として定義されているため、そのままでは判定手続きが明示されていない。
`waitingTiles_ne_nil_iff` を逆向きに使うと、判定対象を実行可能な列挙 `waitingTiles tiles` が
空でないことへ置き換えられる。リストが空でないかは標準の `Decidable` で判定できるため、
`infer_instance` がその手続きを選ぶ。

このインスタンスにより、`IsTenpai tiles` を `decide` や `if` の条件として利用できる。

読むためのLean語彙: `Decidable`, `instance`, `rw`, `infer_instance`, `decide`。
-/
instance decidableIsTenpai (tiles : List Tile) : Decidable (IsTenpai tiles) := by
  rw [← waitingTiles_ne_nil_iff]
  infer_instance

example : decide (IsTenpai [.honor .Red]) = true := by
  native_decide

example : decide (IsTenpai ([] : List Tile)) = false := by
  native_decide

/-- `tiles` から完成面子を1つ取り除いて得られる牌種リストの候補。 -/
def mentsuReductions (tiles : List Tile) : List (List Tile) :=
  mentsuComponentCandidates.filterMap fun mentsu =>
    removeTiles tiles mentsu.tiles

/-- 完成面子を1つ除いても同じ分解数の聴牌形が残るとする旧来の可約性判定。 -/
def CanReduceMentsu (tiles : List Tile) : Prop :=
  1 < tiles.length ∧ IsTenpai tiles ∧
    (mentsuReductions tiles).any (fun remaining =>
      !(waitingTiles remaining).isEmpty &&
        waitCompletionCount remaining == waitCompletionCount tiles) = true

instance decidableCanReduceMentsu (tiles : List Tile) : Decidable (CanReduceMentsu tiles) := by
  unfold CanReduceMentsu
  infer_instance

/-- それ以上、完成面子除去で同じ待ち構造へ小さくできない聴牌形。 -/
def IsIrreducible (tiles : List Tile) (_ : IsTenpai tiles) : Prop :=
  ¬CanReduceMentsu tiles

instance decidableIsIrreducible (tiles : List Tile) (tenpai : IsTenpai tiles) :
    Decidable (IsIrreducible tiles tenpai) := by
  unfold IsIrreducible
  infer_instance

/-- 1枚手牌は単騎として既約である。 -/
theorem singleton_irreducible (tile : Tile) (tenpai : IsTenpai [tile]) :
    IsIrreducible [tile] tenpai := by
  intro reducible
  simpa using reducible.1

/-- 可約なら既約ではない。 -/
theorem not_irreducible_of_canReduceMentsu (tiles : List Tile)
    (tenpai : IsTenpai tiles) (reducible : CanReduceMentsu tiles) :
    ¬IsIrreducible tiles tenpai := by
  exact fun irreducible => irreducible reducible

def manzu (ranks : List Rank) : List Tile :=
  Tile.numberedTiles .Manzu ranks

def souzu (ranks : List Rank) : List Tile :=
  Tile.numberedTiles .Souzu ranks

end WaitCompletionFinder
