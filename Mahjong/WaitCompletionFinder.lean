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

`pairChunkCandidates` は、34種類すべての牌種を雀頭の完成部品へ変換した探索候補である。
`pair_mem_pairChunkCandidates` は任意の雀頭を取りこぼさないこと、
`pair_of_mem_pairChunkCandidates` は候補に雀頭以外が混ざらないことをそれぞれ保証する。
-/

/-- 雀頭候補として使う、全牌種の対子完成部品。 -/
def pairChunkCandidates : List TileChunk :=
  Tile.all.map .pair

example : TileChunk.pair (.honor .Red) ∈ pairChunkCandidates := by
  simp [pairChunkCandidates, Tile.all, Honor.all, TileChunk.pair]

/--
任意の雀頭は `pairChunkCandidates` に含まれる。

これは雀頭候補列挙の完全性を保証する。証明では雀頭から牌種を取り出し、すべての牌種が
`Tile.all` に含まれるという `Tile.mem_all` を使って、その牌種を対子にした候補が存在することを示す。

読むためのLean語彙: `rcases`, `simp`, `∈`。
-/
theorem pair_mem_pairChunkCandidates (pair : Toitsu) :
    (Sum.inl pair : TileChunk) ∈ pairChunkCandidates := by
  rcases pair with ⟨tile⟩
  simp [pairChunkCandidates, Tile.mem_all tile, TileChunk.pair]

/--
`pairChunkCandidates` に含まれる完成部品は、必ず何らかの雀頭である。

これは雀頭候補列挙の健全性を保証し、順子や刻子が雀頭候補へ混ざらないことを示す。
証明ではリストの要素が `Tile.all.map .pair` のどの牌種から作られたかを取り出し、
その牌種の対子を求める雀頭として返す。

読むためのLean語彙: `∃`, `obtain`, `List.mem_map`, `exact`, `rfl`。
-/
theorem pair_of_mem_pairChunkCandidates {chunk : TileChunk}
    (member : chunk ∈ pairChunkCandidates) :
    ∃ pair : Toitsu, chunk = .inl pair := by
  obtain ⟨tile, _, rfl⟩ := List.mem_map.mp member
  exact ⟨.toitsu tile, rfl⟩

/-!
## 完成面子候補の完成部品への持ち上げ

`mentsuChunkCandidates` は、列挙済みの全順子・刻子を、和了分割で使う完成部品へ変換した探索候補である。
`mentsu_mem_mentsuChunkCandidates` は任意の完成面子を取りこぼさないこと、
`mentsu_of_mem_mentsuChunkCandidates` は候補に雀頭が混ざらないことをそれぞれ保証する。
-/

/-- 全順子・刻子を、完成面子側の `TileChunk` として包んだ候補列。 -/
def mentsuChunkCandidates : List TileChunk :=
  (MentsuCandidate.candidates).map fun mentsu => (Sum.inr mentsu : TileChunk)

/--
任意の完成面子候補を包んだ完成部品は `mentsuChunkCandidates` に含まれる。

これは完成面子側の候補列挙の完全性を保証する。先に `MentsuCandidate.mem_candidates` が
全順子・刻子を列挙できることを示しているため、その候補を直和の右側 `.inr` に包めばよい。

読むためのLean語彙: `List.mem_map`, `.mpr`, `_root_`, `exact`, `∈`, `rfl`。
-/
theorem mentsu_mem_mentsuChunkCandidates (mentsu : MentsuCandidate) :
    (Sum.inr mentsu : TileChunk) ∈ mentsuChunkCandidates := by
  exact List.mem_map.mpr ⟨mentsu, _root_.MentsuCandidate.mem_candidates mentsu, rfl⟩

/--
`mentsuChunkCandidates` に含まれる完成部品は、必ず何らかの順子または刻子である。

これは完成面子側の候補列挙の健全性を保証し、雀頭が完成面子候補へ混ざらないことを示す。
証明では `map` 元の `MentsuCandidate` を取り出し、それを求める完成面子として返す。

読むためのLean語彙: `∃`, `obtain`, `List.mem_map`, `.mp`, `exact`, `rfl`。
-/
theorem mentsu_of_mem_mentsuChunkCandidates {chunk : TileChunk}
    (member : chunk ∈ mentsuChunkCandidates) :
    ∃ mentsu : MentsuCandidate, chunk = .inr mentsu := by
  obtain ⟨mentsu, _, rfl⟩ := List.mem_map.mp member
  exact ⟨mentsu, rfl⟩

example : TileChunk.koutsu (.honor .Red) ∈ mentsuChunkCandidates := by
  exact mentsu_mem_mentsuChunkCandidates (.koutsu (.honor .Red))

/-!
## 牌種列を指定個数の完成面子へ分解する

`decomposeMentsu fuel tiles` は、牌種列 `tiles` 全体をちょうど `fuel` 個の順子・刻子へ分解する方法を
すべて列挙する。ここで `fuel` は再帰回数の単なる上限ではなく、求める完成面子の個数である。

`fuel = 0` では牌が残っていない場合だけ、空の分解を1件返す。`fuel + 1` では
`mentsuChunkCandidates` から最初の完成面子を選び、`removeTiles` に成功した候補について、
残りをちょうど `fuel` 個へ再帰的に分解する。除去できない候補や、指定個数を選んだ後に牌が余る枝は捨てる。

結果は `List (List TileChunk)` であり、外側のリストが異なる分解方法、内側のリストが
1つの分解を構成する完成面子列を表す。

読むためのLean語彙: `fuel`, `fuel + 1`, `List.flatten`, `map`, `match`, `[]`, `::`。
-/

/-- 牌種列全体を、ちょうど指定個数の順子・刻子へ分解する方法を列挙する。 -/
def decomposeMentsu : Nat → List Tile → List (List TileChunk)
  | 0, tiles =>
      if tiles.isEmpty then [[]] else []
  | fuel + 1, tiles =>
      List.flatten (mentsuChunkCandidates.map fun mentsu =>
        match removeTiles tiles mentsu.tiles with
        | some remaining =>
            (decomposeMentsu fuel remaining).map fun winningChunks => mentsu :: winningChunks
        | none => [])

    example : decomposeMentsu 0 [] = [[]] := rfl
    example : decomposeMentsu 0 [.numbered .Manzu 0] = [] := rfl

/--
`tiles` をちょうど `fuel` 個の完成面子へ分解できることを表す宣言的な導出関係。

3つの引数は順に、完成面子の個数、分解前の牌種列、分解後の完成面子列を表す。
値を計算して返す関数ではなく、この3者が正しい分解関係にあることの証拠を作る `Prop` である。

- `done`: 0個の完成面子で空の牌種列を空の完成面子列へ分解する。
- `next`: 候補に含まれる完成面子を1つ選び、その牌を除いた残りに対する分解証拠の前へ追加する。

各 `next` は、選んだ値が完成面子候補である証拠と、実際にその牌を除けた証拠を要求する。
そのため、候補でない雀頭や、入力に存在しない牌から分解証拠を作ることはできない。

列挙順序には依存せず、`decomposeMentsu` の健全性・完全性を述べる基準になる。

読むためのLean語彙: 添字付きinductive family, `Prop`, constructor, 暗黙の引数, `.done`, `.next`。
-/
inductive MentsuPartition : Nat → List Tile → List TileChunk → Prop
| done : MentsuPartition 0 [] []
| next {fuel tiles remaining rest} (mentsu : TileChunk)
    (candidate : mentsu ∈ mentsuChunkCandidates)
    (remove : removeTiles tiles mentsu.tiles = some remaining)
    (tail : MentsuPartition fuel remaining rest) :
    MentsuPartition (fuel + 1) tiles (mentsu :: rest)

example :
    MentsuPartition 1
      [.honor .Red, .honor .Red, .honor .Red]
      [TileChunk.koutsu (.honor .Red)] := by
  apply MentsuPartition.next (TileChunk.koutsu (.honor .Red))
  · exact mentsu_mem_mentsuChunkCandidates (.koutsu (.honor .Red))
  · rfl
  · exact .done

/--
完成面子列が `decomposeMentsu` の列挙結果に含まれることと、同じ分解を表す
`MentsuPartition` の証拠を作れることは同値である。

左から右は列挙器の健全性を示す。`fuel` に対する帰納法で、列挙結果を最初に選んだ完成面子と
残りの分解へ分解し、候補所属、牌の除去結果、帰納法で得た残りの証拠から `MentsuPartition.next` を作る。

右から左は列挙器の完全性を示す。`MentsuPartition` の証拠から最初の完成面子、除去結果、
残りの分解証拠を取り出し、帰納法の仮定で残りを列挙結果へ戻して、`map` と `flatten` 内の該当する枝を示す。

`fuel = 0` では、実行器と宣言的関係のどちらも、入力牌列と完成面子列がともに空の場合だけ成立する。
この定理により、後続の証明は実行器のリスト操作を直接追わず、`MentsuPartition` の構築規則を使って
列挙結果の意味を論じられる。

読むためのLean語彙: `↔`, 健全性と完全性, `induction ... generalizing`, `constructor`, `split`,
`List.mem_flatten`, `List.mem_map`, `.mp`, `.mpr`, `subst`, `rw`, `▸`, `rename_i`。
-/
theorem mem_decomposeMentsu_iff (fuel : Nat) (tiles : List Tile)
    (chunks : List TileChunk) :
    chunks ∈ decomposeMentsu fuel tiles ↔ MentsuPartition fuel tiles chunks := by
  induction fuel generalizing tiles chunks with
  | zero =>
      constructor
      · intro member
        simp only [decomposeMentsu] at member
        split at member
        · have tilesEmpty : tiles = [] := List.isEmpty_iff.mp ‹tiles.isEmpty = true›
          subst tiles
          simp only [List.mem_singleton] at member
          subst chunks
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
          obtain ⟨rest, restMember, chunksEq⟩ := List.mem_map.mp member
          exact chunksEq ▸
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
    [TileChunk.koutsu (.honor .Red)] ∈
      decomposeMentsu 1 [.honor .Red, .honor .Red, .honor .Red] := by
  apply (mem_decomposeMentsu_iff 1
    [.honor .Red, .honor .Red, .honor .Red]
    [TileChunk.koutsu (.honor .Red)]).mpr
  apply MentsuPartition.next (TileChunk.koutsu (.honor .Red))
  · exact mentsu_mem_mentsuChunkCandidates (.koutsu (.honor .Red))
  · rfl
  · exact .done

/-- 面子分解の導出は入力牌列の並び替えに依存しない。 -/
theorem MentsuPartition.of_perm {fuel : Nat} {tiles other : List Tile}
    {chunks : List TileChunk} (partition : MentsuPartition fuel tiles chunks)
    (permutation : tiles.Perm other) : MentsuPartition fuel other chunks := by
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

/--
面子分割の全完成部品を牌列へ戻すと、入力牌列と同じ牌種を同じ枚数だけ含む。

リストの順番は一致しなくてもよいため、結論は等号ではなく `List.Perm` で表す。これにより、
分解が入力牌を失ったり、余分な牌を追加したり、同じ牌種の枚数を変えたりしないことが分かる。

証明は分解証拠に対する帰納法で行う。`done` では空列同士の順列を返す。`next` では、
`exists_removeTiles_eq_some_iff_perm` から「先頭面子の牌と除去後の残り」が入力牌列の順列であることを得る。
帰納法の仮定が末尾の完成部品牌と残り牌の順列を保証するので、`List.Perm.append_left` で両側へ
先頭面子の牌を加え、`.trans` で2つの順列関係をつなぐ。

読むためのLean語彙: `List.flatMap`, `List.Perm`, `induction`, `List.Perm.append_left`, `.trans`。
-/
theorem MentsuPartition.tiles_perm {fuel : Nat} {tiles : List Tile}
    {chunks : List TileChunk} (partition : MentsuPartition fuel tiles chunks) :
    (chunks.flatMap TileChunk.tiles).Perm tiles := by
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
      [TileChunk.koutsu (.honor .Red), TileChunk.shuntsu .Manzu ⟨0, by decide⟩]) :
    ([TileChunk.koutsu (.honor .Red), TileChunk.shuntsu .Manzu ⟨0, by decide⟩].flatMap
      TileChunk.tiles).Perm
      [.honor .Red, .numbered .Manzu 0, .honor .Red,
        .numbered .Manzu 1, .honor .Red, .numbered .Manzu 2] := by
  exact partition.tiles_perm

/--
`MentsuPartition` の分解結果に現れるすべての完成部品は、`mentsuChunkCandidates` に含まれる。

これは、分解結果 `chunks` の各要素が順子または刻子の候補として選ばれたことを保証する。
`mentsu_of_mem_mentsuChunkCandidates` と合わせると、面子分解へ雀頭が混ざらないことが分かる。

証明は分解証拠に対する帰納法で行う。`done` の完成面子列は空なので主張は自明である。
`next` では、調べる要素が列の先頭なら構築時に保存された `candidate` を使い、末尾にあれば
残りの分解証拠に対する帰納法の仮定を使う。

読むためのLean語彙: `∀`, `induction`, `intro`, `List.mem_cons`, `rcases`, `rfl | restMember`。
-/
theorem MentsuPartition.all_mentsu {fuel : Nat} {tiles : List Tile}
    {chunks : List TileChunk} (partition : MentsuPartition fuel tiles chunks) :
    ∀ chunk ∈ chunks, chunk ∈ mentsuChunkCandidates := by
  induction partition with
  | done => simp
  | next mentsu candidate remove tail inductionHypothesis =>
      intro chunk member
      rcases List.mem_cons.mp member with rfl | restMember
      · exact candidate
      · exact inductionHypothesis chunk restMember

example
    (partition : MentsuPartition 1
      [.honor .Red, .honor .Red, .honor .Red]
      [TileChunk.koutsu (.honor .Red)]) :
    TileChunk.koutsu (.honor .Red) ∈ mentsuChunkCandidates := by
  exact partition.all_mentsu _ (by simp)

    /--
    面子分割の完成部品列は、順子・刻子だけを持つ `MentsuCandidate` の列として復元できる。

    `all_mentsu` が各要素の候補所属を個別に保証するのに対し、この定理は列全体に対応する
    `candidates` を作り、各要素を直和の右側へ入れ直すと元の `chunks` に一致することを保証する。
    要素の順番と重複も `map` によってそのまま保存される。

    証明は分解証拠に対する帰納法で行う。`done` では空列を返す。`next` では、先頭の候補所属から
    `mentsu_of_mem_mentsuChunkCandidates` で具体的な `MentsuCandidate` を取り出し、帰納法で復元した
    末尾の列へ追加する。

    読むためのLean語彙: `∃`, `List.map`, `induction`, `obtain`, `rfl`, `⟨...⟩`。
    -/
    theorem MentsuPartition.exists_candidates {fuel : Nat} {tiles : List Tile}
      {chunks : List TileChunk} (partition : MentsuPartition fuel tiles chunks) :
      ∃ candidates : List MentsuCandidate,
        chunks = candidates.map fun candidate => (Sum.inr candidate : TileChunk) := by
      induction partition with
      | done => exact ⟨[], rfl⟩
      | next mentsu candidate remove tail inductionHypothesis =>
        obtain ⟨first, rfl⟩ := mentsu_of_mem_mentsuChunkCandidates candidate
        obtain ⟨rest, rfl⟩ := inductionHypothesis
        exact ⟨first :: rest, rfl⟩

    example
        (partition : MentsuPartition 1
          [.honor .Red, .honor .Red, .honor .Red]
          [TileChunk.koutsu (.honor .Red)]) :
        ∃ candidates : List MentsuCandidate,
          [TileChunk.koutsu (.honor .Red)] =
            candidates.map fun candidate => (Sum.inr candidate : TileChunk) := by
      exact partition.exists_candidates

  /--
  面子分割の `fuel` は、生成される完成面子列の長さに一致する。

  したがって `fuel` は探索回数の上限ではなく、この分解が含む完成面子の個数として読める。
  証明は分解証拠に対する帰納法で行う。`done` では両辺が `0` であり、`next` では
  完成面子列の長さと `fuel` がともに1増えるので、残りの分解に対する帰納法の仮定から従う。

  読むためのLean語彙: `List.length`, `induction`, `rfl`, `simp [inductionHypothesis]`。
  -/
  theorem MentsuPartition.chunks_length {fuel : Nat} {tiles : List Tile}
      {chunks : List TileChunk} (partition : MentsuPartition fuel tiles chunks) :
      chunks.length = fuel := by
    induction partition with
    | done => rfl
    | next mentsu candidate remove tail inductionHypothesis =>
        simp [inductionHypothesis]

  example
      (partition : MentsuPartition 1
        [.honor .Red, .honor .Red, .honor .Red]
        [TileChunk.koutsu (.honor .Red)]) :
      [TileChunk.koutsu (.honor .Red)].length = 1 := by
    exact partition.chunks_length

/--
完成面子候補だけからなる部品列を牌列へ平坦化すると、その部品列自身へ正しく分解できる。

入力牌列 `chunks.flatMap TileChunk.tiles` は、各部品を構成する牌を部品の順番どおりに連結した列である。
この定理はその列について `MentsuPartition` の証拠を構築する。入力牌列の任意の並び替えまでを
ここで扱うのではなく、その場合は `MentsuPartition.of_perm` と組み合わせる。

証明は `chunks` に対する帰納法で行う。空列は `MentsuPartition.done` で分解できる。
先頭 `first` がある場合は、`allMentsu` から先頭と末尾の候補所属をそれぞれ取り出し、帰納法で
末尾の分解証拠を作る。連結した牌列から先頭部品の牌を除く計算は `removeTiles_append_left` が保証するため、
これらを `MentsuPartition.next` へ渡せばよい。

読むためのLean語彙: `List.flatMap`, `∀`, `induction`, `have`, `simp`, `.done`, `.next`。
-/
theorem mentsuPartition_flatMap (chunks : List TileChunk)
    (allMentsu : ∀ chunk ∈ chunks, chunk ∈ mentsuChunkCandidates) :
    MentsuPartition chunks.length (chunks.flatMap TileChunk.tiles) chunks := by
  induction chunks with
  | nil => exact .done
  | cons first rest inductionHypothesis =>
      have firstCandidate := allMentsu first (by simp)
      have restCandidates : ∀ chunk ∈ rest, chunk ∈ mentsuChunkCandidates := by
        intro chunk member
        exact allMentsu chunk (by simp [member])
      have tail := inductionHypothesis restCandidates
      have removeFirst :
          removeTiles (first.tiles ++ rest.flatMap TileChunk.tiles) first.tiles =
            some (rest.flatMap TileChunk.tiles) := by
        exact removeTiles_append_left _ _
      exact .next first firstCandidate removeFirst tail

example :
    MentsuPartition 1
      [.honor .Red, .honor .Red, .honor .Red]
      [TileChunk.koutsu (.honor .Red)] := by
  have partition := mentsuPartition_flatMap [TileChunk.koutsu (.honor .Red)] (by
    intro chunk member
    simp only [List.mem_singleton] at member
    subst chunk
    exact mentsu_mem_mentsuChunkCandidates (.koutsu (.honor .Red)))
  simpa [TileChunk.koutsu, TileChunk.tiles, MentsuCandidate.tiles] using partition

/-- 牌種リストを雀頭1つと完成面子列に分解する。 -/
def winningPartitions (tiles : List Tile) : List (List TileChunk) :=
  List.flatten (pairChunkCandidates.map fun pairChunk =>
    match removeTiles tiles pairChunk.tiles with
    | some remaining =>
        (decomposeMentsu (remaining.length / mentsuTileCount) remaining).map fun winningChunks =>
          pairChunk :: winningChunks
    | none => [])

/-- 雀頭1個を除き、残りを完成面子へ分解できる通常和了分割の宣言的仕様。 -/
inductive WinningPartition (tiles : List Tile) : List TileChunk → Prop
| intro {remaining rest} (pair : TileChunk)
    (pairCandidate : pair ∈ pairChunkCandidates)
    (removePair : removeTiles tiles pair.tiles = some remaining)
    (mentsuPartition : MentsuPartition (remaining.length / mentsuTileCount) remaining rest) :
    WinningPartition tiles (pair :: rest)

/-- `winningPartitions` は通常和了分割の宣言的仕様を過不足なく列挙する。 -/
theorem mem_winningPartitions_iff (tiles : List Tile) (chunks : List TileChunk) :
    chunks ∈ winningPartitions tiles ↔ WinningPartition tiles chunks := by
  constructor
  · intro member
    simp only [winningPartitions] at member
    obtain ⟨generated, generatedMember, member⟩ := List.mem_flatten.mp member
    obtain ⟨pair, pairCandidate, rfl⟩ := List.mem_map.mp generatedMember
    cases removeEq : removeTiles tiles pair.tiles with
    | none => simp [removeEq] at member
    | some remaining =>
      rw [removeEq] at member
      obtain ⟨rest, restMember, chunksEq⟩ := List.mem_map.mp member
      exact chunksEq ▸
        WinningPartition.intro pair pairCandidate removeEq
          ((mem_decomposeMentsu_iff _ _ _).mp restMember)
  · intro partition
    cases partition with
    | intro pair pairCandidate removePair partition =>
        rename_i remaining rest
        apply List.mem_flatten.mpr
        refine ⟨(decomposeMentsu (remaining.length / mentsuTileCount) remaining).map
          fun chunks => pair :: chunks, ?_, ?_⟩
        · apply List.mem_map.mpr
          exact ⟨pair, pairCandidate, by simp [removePair]⟩
        · exact List.mem_map.mpr
            ⟨rest, (mem_decomposeMentsu_iff _ _ _).mpr partition, rfl⟩

/-- 通常和了分割の導出は入力牌列の並び替えに依存しない。 -/
theorem WinningPartition.of_perm {tiles other : List Tile} {chunks : List TileChunk}
    (partition : WinningPartition tiles chunks) (permutation : tiles.Perm other) :
    WinningPartition other chunks := by
  cases partition with
  | intro pair pairCandidate removePair mentsuPartition =>
      rename_i remaining rest
      have removedPerm : (pair.tiles ++ remaining).Perm tiles :=
        (exists_removeTiles_eq_some_iff_perm tiles pair.tiles remaining).mp
          ⟨remaining, removePair, .refl remaining⟩
      obtain ⟨output, removeOther, outputPerm⟩ :=
        (exists_removeTiles_eq_some_iff_perm other pair.tiles remaining).mpr
          (removedPerm.trans permutation)
      have sameLength : output.length = remaining.length := outputPerm.length_eq
      rw [← sameLength] at mentsuPartition
      exact .intro pair pairCandidate removeOther
        (mentsuPartition.of_perm outputPerm.symm)

/-- 通常和了分割の全チャンク牌は入力牌列と多重集合として一致する。 -/
theorem WinningPartition.tiles_perm {tiles : List Tile} {chunks : List TileChunk}
    (partition : WinningPartition tiles chunks) :
    (chunks.flatMap TileChunk.tiles).Perm tiles := by
  cases partition with
  | intro pair pairCandidate removePair mentsuPartition =>
      rename_i remaining rest
      have removedPerm : (pair.tiles ++ remaining).Perm tiles :=
        (exists_removeTiles_eq_some_iff_perm tiles pair.tiles remaining).mp
          ⟨remaining, removePair, .refl remaining⟩
      exact (List.Perm.append_left pair.tiles mentsuPartition.tiles_perm).trans removedPerm

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

/-- 待ちの意味論は牌姿リストの並び順に依存しない。 -/
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
      obtain ⟨chunks, chunksMember⟩ := List.exists_mem_of_ne_nil _ nonempty
      have partition := (mem_winningPartitions_iff _ _).mp chunksMember
      have otherMember := (mem_winningPartitions_iff _ _).mpr
        (partition.of_perm (permutation.cons candidate))
      have otherNonempty : winningPartitions (candidate :: other) ≠ [] :=
        List.ne_nil_of_mem otherMember
      simp [otherNonempty]

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

/-- `waitingTiles` は `IsWaitFor` をちょうど判定する。 -/
theorem mem_waitingTiles_iff (tiles : List Tile) (candidate : Tile) :
    candidate ∈ waitingTiles tiles ↔ IsWaitFor tiles candidate := by
  by_cases legal : IsLegalTenpaiHand tiles
  · simp [waitingTiles, legal, Tile.mem_all, IsWaitFor, IsStandardAgari,
      Bool.and_eq_true]
  · simp [waitingTiles, legal, IsWaitFor]

/-- `waitingTiles` が空でないことと意味論上の聴牌は同値である。 -/
theorem waitingTiles_ne_nil_iff (tiles : List Tile) :
    waitingTiles tiles ≠ [] ↔ IsTenpai tiles := by
  constructor
  · intro nonempty
    obtain ⟨candidate, member⟩ := List.exists_mem_of_ne_nil _ nonempty
    exact ⟨candidate, (mem_waitingTiles_iff tiles candidate).mp member⟩
  · rintro ⟨candidate, valid⟩ empty
    have member := (mem_waitingTiles_iff tiles candidate).mpr valid
    simp [empty] at member

/-- 待ち牌と、その待ち牌を加えた和了形の正規化済み分割を列挙する。 -/
def findWaitCompletions (tiles : List Tile) : List WaitCompletion :=
  ((waitingTiles tiles).flatMap fun wait =>
    (winningPartitions (wait :: tiles)).map fun winningChunks =>
      { wait, winningChunks := TileChunk.canonicalize winningChunks }).dedup

/--
`completion` が牌姿 `tiles` の待ちと和了分割を表すことの宣言的仕様。

Finder が内部で見つける分割は雀頭を先頭に持つが、外部へ返す際にはチャンク順を正規化する。
そのため仕様は、正規化前の `rawChunks` の存在として述べる。
-/
inductive CompletionFor (tiles : List Tile) : WaitCompletion → Prop
| intro (wait : Tile) (rawChunks : List TileChunk)
    (waitFor : IsWaitFor tiles wait)
    (partition : WinningPartition (wait :: tiles) rawChunks) :
    CompletionFor tiles
      { wait, winningChunks := TileChunk.canonicalize rawChunks }

/-- completionの意味論は牌姿リストの並び順に依存しない。 -/
theorem CompletionFor.of_perm {tiles other : List Tile} {completion : WaitCompletion}
    (valid : CompletionFor tiles completion) (permutation : tiles.Perm other) :
    CompletionFor other completion := by
  cases valid with
  | intro wait rawChunks waitFor partition =>
      exact .intro wait rawChunks (waitFor.of_perm permutation)
        (partition.of_perm (permutation.cons wait))

/-- `findWaitCompletions` は宣言的な待ちと和了分割を過不足なく列挙する。 -/
theorem mem_findWaitCompletions_iff (tiles : List Tile) (completion : WaitCompletion) :
    completion ∈ findWaitCompletions tiles ↔ CompletionFor tiles completion := by
  rw [findWaitCompletions, List.mem_dedup]
  constructor
  · intro member
    obtain ⟨wait, waitMember, completionMember⟩ := List.mem_flatMap.mp member
    obtain ⟨rawChunks, partitionMember, completionEq⟩ := List.mem_map.mp completionMember
    rw [← completionEq]
    exact .intro wait rawChunks ((mem_waitingTiles_iff tiles wait).mp waitMember)
      ((mem_winningPartitions_iff _ _).mp partitionMember)
  · intro valid
    cases valid with
    | intro wait rawChunks waitFor partition =>
        apply List.mem_flatMap.mpr
        refine ⟨wait, (mem_waitingTiles_iff tiles wait).mpr waitFor, ?_⟩
        exact List.mem_map.mpr
          ⟨rawChunks, (mem_winningPartitions_iff _ _).mpr partition, rfl⟩

/-!
## 分解に関する既約性

`waitCompletionCount` は待ち牌と和了形の組を数える。メンツを1つ除いた
聴牌形が同じ個数の分解を持つなら、その手牌はメンツ除去により可約である。
待ちでない牌列を既約とは扱わない。

これは分解数だけを比較する旧来の近似である。分類で使う根源的な既約性は
`WaitReadingCode.CanReduceMentsuPreservingWaitCores` が待ち核集合を比較する。
-/
def waitCompletionCount (tiles : List Tile) : Nat :=
  (findWaitCompletions tiles).length

instance decidableIsTenpai (tiles : List Tile) : Decidable (IsTenpai tiles) := by
  rw [← waitingTiles_ne_nil_iff]
  infer_instance

/-- `tiles` から完成面子を1つ取り除いて得られる牌種リストの候補。 -/
def mentsuReductions (tiles : List Tile) : List (List Tile) :=
  mentsuChunkCandidates.filterMap fun mentsu =>
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
