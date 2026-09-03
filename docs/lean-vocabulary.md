# Lean語彙

この文書は、Leanを知らない読者が麻雀待ち分類の説明を読むための最小限の語彙を管理する。
語彙は初出時にここで説明し、各定理のコメントではその定理固有の意味に集中する。

## 最小語彙

### namespace

`namespace Tile` から `end Tile` までの内側では、名前が `Tile` の文脈に入る。
そのため、内側で単に `all` と書かれている場合、文脈上は `Tile.all` を指す。
名前空間は、`Tile.all`、`Suit.all`、`Honor.all` のように、同じ短い名前を安全に使い分けるための仕組みである。
同じ仕組みで、`namespace Chunk` の内側では `take` は `Chunk.take` を指す。

### open

`open WaitReadingCode` は、`WaitReadingCode` 名前空間の中にある名前を短く書けるようにする。
たとえば `WaitReadingCode.findIrreducibleWaitReadings` を、文脈によっては `findIrreducibleWaitReadings` と書ける。

### def

`def` は定義を作る。たとえば `Tile.all` は、34種類すべての牌種を標準順に並べたリストとして定義される。

### let

`let name := value` は、式の途中で一時的な名前を付ける構文である。
`waitProfilesOfIrreducibleReading` では、核成分列の種類を `coreKinds`、除去した面子の種類を `removedKinds` として使う。

### noncomputable def

`noncomputable def` は、数学的には定義できるが、Leanが通常の実行用プログラムとして直接扱うとは限らない定義である。
ここでは、有限集合 `Finset` をリストに変換して探索する処理に使われている。
性質を述べたり証明したりするためには使えるが、通常の実行用関数とは区別して読む。

### abbrev

`abbrev` は略記を作る。たとえば `deckSize` は `Tile.count * copiesPerTile` の略記である。
長い型や式に読みやすい名前を付ける目的で使われる。

### inductive

`inductive` は、いくつかの作り方を列挙して新しい型を定義する。
たとえば `MentsuCandidate` は、順子を表す `shuntsu` と刻子を表す `koutsu` の2通りで作られる。

### theorem

`theorem` は、Leanに確認させる主張を作る。定義が「値や計算方法」を与えるのに対して、定理は
「その値や計算方法について成り立つ性質」を与える。

### Prop

`Prop` は、真か偽かを持つ命題の型である。
`MentsuCandidate.IsShuntsu : MentsuCandidate → Prop` は、完成面子候補が順子である、という命題を返す。

### Decidable

`Decidable P` は、命題 `P` が成り立つかどうかをLeanが判定できることを表す。
`instance ... : Decidable (...)` は、その命題を条件分岐や計算で使えるようにするための登録である。

### example

`example` は、名前を付けずにLeanへ確認させる小さな主張である。
ドキュメントでは、定義が具体的な入力に対してどう振る舞うかを、Leanが検査するサンプルとして使う。

### structure

`structure` は、複数の情報を名前付きの部品としてまとめる型を作る。
たとえば `Chunk` は、物理牌の有限集合 `tiles` と、それが空でないことを示す `nonempty` をまとめた型である。

### class

`class` は、複数の型に共通する操作や性質を表すインターフェースを作る。
`HasTilePattern` は、「この型の値から牌種列を取り出せる」という共通操作 `tiles` を表す型クラスである。

### 型引数 `{α : Type}`

`α` は、具体的な型をあとから入れるための名前である。`{α : Type}` は、`α` が型であることを表す。
波括弧 `{...}` で囲まれているため、多くの場合はLeanが文脈から自動で補う。

### Fin

`Fin n` は、`0` 以上 `n` 未満の自然数を表す型である。
開始位置を `Fin` で持つと、順子や両面ターツで存在しない開始位置を型で除外できる。

### 型クラス引数 `[HasTilePattern α]`

角括弧 `[HasTilePattern α]` は、型 `α` が `HasTilePattern` のインターフェースを持っていることを要求する。
この引数があると、Leanは `α` の値から `HasTilePattern.tiles` で牌種列を取り出せるものとして扱える。

### instance

`instance` は、ある型が型クラスのインターフェースを満たすことをLeanに登録する。
たとえば `instance : HasTilePattern Taatsu where ...` は、`Taatsu` から牌種列を取り出す方法を登録している。

### `List Tile`

`List Tile` は、牌種 `Tile` の列を表す型である。
ターツ、対子、順子のような部品は、それぞれを構成する牌種列として `List Tile` に変換される。

### `++`

`xs ++ ys` は、リスト `xs` の後ろにリスト `ys` を連結する記法である。
`WaitPattern.tiles` では、対子の牌種列とターツの牌種列を連結して、抽出パターン全体に必要な牌種列を作る。

### Bool

`Bool` は、`true` または `false` のどちらかを持つ型である。
`Taatsu.penchan` では、`false` が低い側の辺張、`true` が高い側の辺張を表す。

### Boolの `&&`、`!`、`==`、`!=`

`a && b` はBool値 `a` と `b` が両方とも `true` かを計算し、`!a` はBool値を反転する。
`a == b` は2つの値が等しいかをBool値として計算し、`a != b` は異なるかを計算する。
`canReduceMentsuPreservingWaitCores` では、除去後の待ち牌列が空でないことと、除去前後の待ち核集合が
等しいことを `&&` で同時に要求する。

### 直和 `⊕`

`A ⊕ B` は、A型の値またはB型の値のどちらかを持つ型である。
`TileChunk := Toitsu ⊕ MentsuCandidate` は、完成部品が雀頭または完成面子候補のどちらかであることを表す。

### `.inl` と `.inr`

`.inl value` は直和 `A ⊕ B` の左側、`.inr value` は右側に値を入れる。
`TileChunk.pair` は雀頭を `.inl` に入れ、`TileChunk.shuntsu` と `TileChunk.koutsu` は完成面子候補を `.inr` に入れる。

### 部分型 `{ x : α // 条件 }`

`{ x : α // 条件 }` は、型 `α` の値のうち、条件を満たすものだけを表す型である。
`tile : { pt : PhysicalTile // pt ∈ chunk.tiles }` は、`tile` が単なる物理牌ではなく、
`chunk.tiles` に含まれていることも一緒に持っている値である、という意味になる。

### 直積 `×`

`A × B` は、A型の値とB型の値をペアで持つ型である。
`PhysicalTile × Finset PhysicalTile` は、取り出した物理牌と、残りの物理牌集合をまとめて返す型である。

### Option

`Option A` は、A型の値が得られた場合と、得られなかった場合を表す型である。
`some value` は成功して値があること、`none` は失敗して値がないことを表す。
`takeTileFrom` では、指定した牌種の物理牌が見つかれば `some`、見つからなければ `none` を返す。

### match

`match` は、値の形によって処理を分ける構文である。
`match ... with | some tile => ... | none => ...` は、探索に成功した場合と失敗した場合を分けている。

### if

`if condition then a else b` は、条件が成り立つかどうかで返す値を分ける構文である。
`waitProfilesOfIrreducibleReading` では、特定の部品種別が含まれるかどうかで、観測基本形を追加するか空リストにする。

### 証拠付き `if`

`if proof : proposition then a else b` は、命題が成り立つかを調べると同時に、then側でその証拠を
`proof` という名前で使える条件分岐である。`determineReducibility` の `if tenpai : IsTenpai tiles` では、
聴牌の場合に得た証拠 `tenpai` を、証拠を要求する `reducibility tiles tenpai` へ渡している。

### filter

`xs.filter p` は、リスト `xs` のうち条件 `p` を満たす要素だけを残す。
`coreKinds.filter ...` は、核成分列の中に特定の部品種別がいくつあるかを数えるために使われる。

### List.any

`xs.any p` は、リスト `xs` の要素のうち、条件 `p` が `true` になるものが1つでもあるかを計算する。
`canReduceMentsuPreservingWaitCores` では、完成面子を1つ除いた候補のうち、待ち核集合を保つものが
1つでも存在するかを調べる。

### map

`xs.map f` は、リスト `xs` の各要素に関数 `f` を適用し、結果を同じ順番で並べたリストを作る。
`waitCores` では、各 `IrreducibleWaitReading` から待ち牌と核成分列だけを持つ `WaitCore` を作る。

### flatMap

`xs.flatMap f` は、リストの各要素に `f` を適用してリストを作り、それらを1つにつなげる。
`observedWaitProfiles` では、各待ち核から得られる観測基本形列をまとめて1つの列にする。

### パイプ演算子 `|>`

`value |> f` は `f value` と同じ意味で、左側の値を右側の関数へ渡す。
複数行で続けると、前の処理結果を次の処理へ順番に渡す流れとして読める。
`waitCores` では、Readingの列を待ち核の列へ変換し、その結果を重複排除と整列の処理へ渡す。

### `.1`

`.1` は、ペアの1番目の要素を取り出す記法である。
`(chunk.take tile).1` は、`chunk.take tile` が返したペアのうち、取り出した牌の側を表す。

### `.2`

`.2` は、ペアの2番目の要素を取り出す記法である。
`(chunk.take tile).2` は、`chunk.take tile` が返したペアのうち、残りの牌集合の側を表す。

### `@[simp]`

`@[simp]` は、その定理を `simp` が使える単純化規則として登録する印である。
たとえば `take_fst` に付けると、`simp` が `(chunk.take tile).1` を `tile` に書き換えられるようになる。

### by

`by` は、ここから証明を書く、という合図である。`theorem ... := by` の後には、Leanに目標を確認させながら
証明を進める命令を並べる。

### tactic

タクティクは、証明中の目標を少しずつ変形したり、分解したり、解決したりする命令である。
`cases`、`simp`、`left`、`exact` はタクティクの例である。

### cases

`cases tile with` は、`tile` がどの形で作られた値かによって証明を分ける。
`Tile` は数牌を表す `numbered suit rank` と字牌を表す `honor honor` の2通りで作られるため、
`| numbered suit rank =>` が数牌の場合、`| honor honor =>` が字牌の場合の証明になる。

`cases kind` のように `with` を省略すると、分岐名を明示せず、Leanに各場合を順に作らせる。

### constructor

`constructor` は、目標が複数の部品からできているときに、それぞれの部品を別々の目標へ分けるタクティクである。
`P ↔ Q` の証明では、`P → Q` と `Q → P` の2つの方向に分ける。

### intro

`intro` は、仮定を受け取って名前を付けるタクティクである。
`expectedKind_iff` では、`expectedKind profiles = some kind` という計算結果や、`Classifies profiles kind` という分類証拠を受け取る。

### unfold

`unfold` は、定義を展開するタクティクである。
`unfold expectedKind at result` は、仮定 `result` の中に出てくる `expectedKind` の定義を展開する。

### split

`split` は、`if` や `match` による分岐を証明中でも場合分けするタクティクである。
`expectedKind_iff` では、`expectedKind` の分岐を順に開いて、各分類規則に対応させている。

### rcases

`rcases` は、複数の部品を持つ値を分解して、それぞれの部品に名前を付けるタクティクである。
`rcases shuntsuPattern with ⟨suit, start⟩` は、順子パターンからスート `suit` と開始位置 `start` を取り出している。

### simp

`simp` は、定義を展開したり、既知の事実で式を書き換えたりして、目標を単純な形にするタクティクである。
`simp only [all, List.mem_append, List.mem_flatMap]` のように `only` を付けると、角括弧 `[...]` に並べた
定義や定理だけを使う。

`simp [all]` のように `only` を付けない場合は、角括弧内の指定に加えて、Leanが標準的に知っている単純化規則も使う。

`simp [tiles, Shuntsu.tiles] at honor_mem` のように `at` を付けると、現在の目標ではなく、手元にある仮定
`honor_mem` を単純化する。

### simp_all

`simp_all` は、現在の目標だけでなく、手元の仮定も使って単純化するタクティクである。
`expectedKind_iff` では、`Classifies` の各場合から得られる仮定を使い、`expectedKind` が対応する分類名を返すことを確認している。

### at

`at` は、タクティクをどこに適用するかを指定する構文である。
`simp ... at honor_mem` は、`honor_mem` という仮定を対象にして単純化する、という意味になる。

### `<;>`

`<;>` は、左側のタクティクでできたすべての目標に、右側のタクティクを続けて適用する記号である。
たとえば `cases kind <;> simp [all]` は、`kind` を分類名ごとに場合分けし、それぞれの分岐を
`simp [all]` で確認する、という意味になる。

### 角括弧 `[...]`

`simp only [...]` の角括弧は、`simp` に使わせる定義や定理の一覧を表す。
たとえば `[all, List.mem_append, List.mem_flatMap]` は、現在の名前空間の `all` と、リストの連結・`flatMap` に関する
所属条件の定理を使う、という指定である。

### left

`left` は、目標が「A または B」の形になっているとき、Aの側を示すと宣言するタクティクである。
`Tile.mem_all` では、`Tile.all` が `数牌一覧 ++ 字牌一覧` なので、数牌の場合に「左側の数牌一覧に含まれる」ことを選ぶ。

### exact

`exact` は、残った目標を満たす証拠をその場で与えるタクティクである。
証明の最後に「これが求められていた証拠です」とLeanへ渡す役割を持つ。

### refine と `?_`

`refine` は、証拠の大枠だけを先に与え、まだ埋めていない部分を後続の目標として残すタクティクである。
`?_` は、その未完成部分を表す穴である。`mem_candidates` では、順子候補列に入る証拠のうち、
スート側を先に与え、開始位置側の証拠を `?_` として後で `exact` で埋めている。

### rfl

`rfl` は、定義を展開すると左辺と右辺が同じ形になる等式を証明するタクティクである。
`deck_cardinality` では、`deckSize` などの略記を展開した後、残った等式が定義上同じであることを確認する。

### Finset

`Finset` は、重複のない有限集合を表す型である。`deck : Finset PhysicalTile` は、山を構成する物理牌全体を
有限集合として持つ、という意味になる。

### `.card`

`.card` は有限集合の要素数を取り出す。`deck.card` は、有限集合 `deck` に含まれる物理牌の枚数を表す。

### `∈`

`tile ∈ all` は、`tile` がリストや集合 `all` に含まれる、という意味である。
`Tile.mem_all` の主張 `tile ∈ all` は、任意の牌種 `tile` が標準列挙 `Tile.all` に含まれることを表す。

### `↔`

`P ↔ Q` は、命題 `P` と命題 `Q` が同値であることを表す。
`expectedKind_iff` では、参照実装 `expectedKind profiles = some kind` と、宣言的仕様 `Classifies profiles kind` が同値であることを示す。

### `¬`

`¬P` は、命題 `P` が成り立たない、という意味である。
`¬candidate.IsShuntsu` は、その完成面子候補が順子ではないことを表す。

### `∉`

`x ∉ xs` は、`x` がリストや集合 `xs` に含まれない、という意味である。
`take_snd_not_mem` の主張は、取り出した牌が残りの集合にはもう含まれないことを表す。
