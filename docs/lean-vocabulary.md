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

### `let rec`

`let rec name ...` は、定義の途中で、自分自身を呼び出せる局所的な再帰関数を作る。
`waitReadings` の `selectCompletedChunk` は、完成部品列の先頭を調べた後、残りの列に対して自分自身を呼び出す。

### fuel

`fuel` はLeanの予約語ではなく、再帰処理をあと何段進めるかを表す引数によく使う名前である。
自然数の `fuel` を再帰ごとに減らせば、Leanは処理が停止することを確認できる。
`decomposeMentsu` では停止のためだけの上限ではなく、分解に使う完成面子の個数も表す。

### `fuel + 1` パターン

自然数をパターン照合するとき、`0` はゼロの場合、`fuel + 1` は1以上の場合を表す。
後者では、元の数より1小さい自然数を `fuel` として再帰呼び出しに使える。

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

### 添字付きinductive family

`MentsuPartition : Nat → List Tile → List TileChunk → Prop` のように、引数によって異なる命題や型を返す
`inductive` 定義を、添字付きinductive familyと呼ぶ。constructorごとに、どの引数の組について値を
作れるかを制限できる。`MentsuPartition.done` は `0, [], []` の組だけを作り、`next` は面子数を1増やす。

### inductive型のconstructor

inductive型のconstructorは、その型の値や証拠を作る方法である。`MentsuPartition.done`と
`MentsuPartition.next`は、正しい面子分解の証拠を作る2つの方法を表す。
証明タクティクの`constructor`とは同じ語を使うが、ここではinductive定義に並ぶ`done`や`next`を指す。

### 暗黙の引数 `{...}`

定義やconstructorの引数を波括弧`{...}`で囲むと、多くの場合は他の引数や期待される型からLeanが値を補う。
`MentsuPartition.next`の`fuel`、`tiles`、`remaining`、`rest`は、完成面子、除去結果、再帰的な分解証拠から推論される。

### theorem

`theorem` は、Leanに確認させる主張を作る。定義が「値や計算方法」を与えるのに対して、定理は
「その値や計算方法について成り立つ性質」を与える。

### `Function.Injective`

`Function.Injective f` は、関数 `f` が異なる入力を同じ出力へ潰さないことを表す。
言い換えると、`f a = f b` なら必ず `a = b` になるという主張である。
`TileChunk.orderKey_injective` は、完成部品の数値キーが等しければ、元の完成部品も等しいことを保証する。

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

### リストの `[]` と `::`

`[]` は空リスト、`first :: rest` は先頭要素 `first` と残りのリスト `rest` からなるリストを表す。
リストを `match` するときは、この2つの形に分けることで、空の場合と先頭要素がある場合を処理できる。

### `++`

`xs ++ ys` は、リスト `xs` の後ろにリスト `ys` を連結する記法である。
`WaitPattern.tiles` では、対子の牌種列とターツの牌種列を連結して、抽出パターン全体に必要な牌種列を作る。

### `List.Perm`

`xs.Perm ys` は、リスト `xs` と `ys` が同じ要素を同じ個数だけ含み、順番だけが異なり得ることを表す。
集合と違って重複数も保存するため、`[a, a, b]` と `[a, b]` は順列関係にならない。

### `List.Perm.append_left`

`List.Perm.append_left prefix proof` は、`xs.Perm ys` の証拠 `proof` から、両方の先頭へ同じ列
`prefix` を連結した `(prefix ++ xs).Perm (prefix ++ ys)` の証拠を作る。
`MentsuPartition.tiles_perm` では、残り牌について得た順列の両側へ、現在の完成面子の牌を加える。

### `List.Perm.nil_eq`

`List.Perm.nil_eq proof` は、空列とあるリストが順列関係にあるという証拠から、そのリストも空列であると示す。
空列は要素を持たず、`List.Perm` は要素とその個数を保存するためである。`MentsuPartition.of_perm` の
`done` の場合に、並べ替え後の入力も空であることを確認する。

### `List.Perm.length_eq`

`proof.length_eq` は、`xs.Perm ys` の証拠 `proof` から `xs.length = ys.length` を得る。
順列は要素の順番だけを変え、追加や削除をしないため、リストの長さも保存する。
`WinningPartition.of_perm` では、雀頭を除いた新旧の残り牌列から計算される面子数の型を揃えるために使う。

### mergeSort

`xs.mergeSort le` は、比較関数 `le` を使ってリスト `xs` を整列する。
`TileChunk.canonicalize` では、完成部品を `orderKey` の昇順に並べるために使う。
整列は要素を追加・削除せず、入力リストの順列を返す。

### Bool

`Bool` は、`true` または `false` のどちらかを持つ型である。
`Taatsu.penchan` では、`false` が低い側の辺張、`true` が高い側の辺張を表す。

### Boolの `&&`、`!`、`==`、`!=`

`a && b` はBool値 `a` と `b` が両方とも `true` かを計算し、`!a` はBool値を反転する。
`a == b` は2つの値が等しいかをBool値として計算し、`a != b` は異なるかを計算する。
`canReduceMentsuPreservingWaitCores` では、除去後の待ち牌列が空でないことと、除去前後の待ち核集合が
等しいことを `&&` で同時に要求する。

`Bool.and_eq_true` は、`a && b = true` を `a = true ∧ b = true` として読み替える定理である。
`mem_waitingTiles_iff` では、実行器が使うBoolの条件を、`IsWaitFor` が使う命題の論理積へ対応させる。

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

### Option.map

`option.map f` は、`option` が `some value` なら `some (f value)` を返し、`none` ならそのまま `none` を返す。
`componentAfterRemovingWait` では、部品種別を得られた場合だけ、残った具体牌と組み合わせる。

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

### List.erase

`xs.erase x` は、リスト `xs` で最初に現れる `x` を1つだけ取り除く。
同じ値が複数あっても、残りはそのまま保持する。対子 `55m` から `5m` を `erase` すると、単騎の `5m` が1枚残る。

### List.any

`xs.any p` は、リスト `xs` の要素のうち、条件 `p` が `true` になるものが1つでもあるかを計算する。
`canReduceMentsuPreservingWaitCores` では、完成面子を1つ除いた候補のうち、待ち核集合を保つものが
1つでも存在するかを調べる。

### List.foldl

`xs.foldl f initial` は、初期値 `initial` から始め、リスト `xs` の要素を左から順に関数 `f` へ渡して
1つの値へ畳み込む。`componentProduct` では初期値を1とし、各部品種別に割り当てた素数を順に掛ける。

### map

`xs.map f` は、リスト `xs` の各要素に関数 `f` を適用し、結果を同じ順番で並べたリストを作る。
`waitCores` では、各 `IrreducibleWaitReading` から待ち牌と核成分列だけを持つ `WaitCore` を作る。

### `List.mem_map`

`List.mem_map` は、値 `result` が `xs.map f` に含まれることを、元のリスト `xs` に
`f source = result` となる要素 `source` が存在することとして読み替える定理である。
`pair_of_mem_pairChunkCandidates` では、雀頭候補が `Tile.all` のどの牌種から作られたかを取り出す。

### `.mp` と `.mpr`

同値 `P ↔ Q` の証拠に対して、`.mp` は `P` の証拠を `Q` の証拠へ、`.mpr` は逆向きに変換する。
`List.mem_map.mp` は写像後のリストに含まれることから写像元を取り出し、`List.mem_map.mpr` は
写像元とその所属証拠から、写像後のリストに含まれることを示す。

### `_root_`

`_root_.Name` は、現在の名前空間の外にある最上位の名前 `Name` を明示する書き方である。
`WaitCompletionFinder` 名前空間の中から `_root_.MentsuCandidate.mem_candidates` と書くと、
最上位の `MentsuCandidate` 名前空間にある定理を指定できる。

### flatMap

`xs.flatMap f` は、リストの各要素に `f` を適用してリストを作り、それらを1つにつなげる。
`observedWaitProfiles` では、各待ち核から得られる観測基本形列をまとめて1つの列にする。

### List.flatten

`List.flatten xss` は、リストのリスト `xss` に含まれる内側のリストを順番につなぎ、1つのリストにする。
`decomposeMentsu` では、最初に選ぶ完成面子候補ごとに得られた分解方法の列を、すべてまとめるために使う。

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

### native_decide

`native_decide` は、真偽を計算できる命題をLeanの実行系で評価し、その計算結果が真であることを証明する
タクティクである。有限個の値についてすべての場合を確認できる主張に向いている。
`TileChunk.orderKey_injective` では、有限個の完成部品の組合せを計算し、同じキーを持つ異なる部品がないことを確認する。

### cases

`cases tile with` は、`tile` がどの形で作られた値かによって証明を分ける。
`Tile` は数牌を表す `numbered suit rank` と字牌を表す `honor honor` の2通りで作られるため、
`| numbered suit rank =>` が数牌の場合、`| honor honor =>` が字牌の場合の証明になる。

`cases kind` のように `with` を省略すると、分岐名を明示せず、Leanに各場合を順に作らせる。

`cases equation : expression with` は、`expression` の値で場合分けすると同時に、各場合の計算結果を
`equation` という等式として残す。`mem_winningPartitions_iff` の
`cases removeEq : removeTiles tiles pair.tiles` では、除去の失敗と成功に分け、成功時の等式を
`WinningPartition.intro` へ渡す。

### induction

`induction xs with` は、再帰的に作られた値 `xs` の構造に沿って命題を証明するタクティクである。
リストの場合は、空列 `nil` の場合と、先頭要素を残りの列へ加えた `cons` の場合に分ける。
`cons` の場合には、残りの列について同じ命題が成り立つという帰納法の仮定も使える。
`removeTiles_append_left` では、除去対象の牌を先頭から1枚ずつ処理する再帰と同じ構造で証明を進める。

### `List.length`

`xs.length` または `List.length xs` は、リスト `xs` の要素数を返す。空列の長さは `0` で、
`first :: rest` の長さは `rest.length + 1` である。`MentsuPartition.chunks_length` では、
分解証拠へ完成面子を1つ追加するたび、結果列の長さと `fuel` がともに1増えることを使う。

### `induction ... generalizing`

`induction fuel generalizing tiles chunks` は、`fuel`について帰納法を行うとき、`tiles`と`chunks`を
特定の値に固定せず、任意の値について使える帰納法の仮定を作る。`mem_decomposeMentsu_iff`では、
再帰呼び出しで残りの牌種列と完成面子列へ変わるため、この一般化が必要になる。

### constructor

`constructor` は、目標が複数の部品からできているときに、それぞれの部品を別々の目標へ分けるタクティクである。
`P ↔ Q` の証明では、`P → Q` と `Q → P` の2つの方向に分ける。

### intro

`intro` は、仮定を受け取って名前を付けるタクティクである。
`expectedKind_iff` では、`expectedKind profiles = some kind` という計算結果や、`Classifies profiles kind` という分類証拠を受け取る。

### have

`have name : proposition := proof` は、証明の途中で補助的な事実を示し、`name` を付けて後から使えるようにする。
型をLeanが推論できる場合は、`have name := proof` のように命題を省略できる。
`mentsuPartition_flatMap` では、先頭の候補所属、末尾の分解証拠、先頭部品を除いた計算結果を順に保持する。

### apply

`apply theoremName` は、現在の目標を結論として持つ定理を使い、その定理に必要な仮定を新しい目標にする。
`canonicalize_eq_of_perm` では、整列済みの順列が等しいという一般定理を使い、その条件を順番に証明する。

### unfold

`unfold` は、定義を展開するタクティクである。
`unfold expectedKind at result` は、仮定 `result` の中に出てくる `expectedKind` の定義を展開する。

### split

`split` は、`if` や `match` による分岐を証明中でも場合分けするタクティクである。
`expectedKind_iff` では、`expectedKind` の分岐を順に開いて、各分類規則に対応させている。

### by_cases

`by_cases proof : proposition` は、命題 `proposition` が成り立つ場合と成り立たない場合に証明を分ける。
前者では `proof : proposition`、後者では `proof : ¬proposition` を仮定として使える。
`mem_waitingTiles_iff` では、入力が合法な聴牌手である場合とそうでない場合に分ける。

### rcases

`rcases` は、複数の部品を持つ値を分解して、それぞれの部品に名前を付けるタクティクである。
`rcases shuntsuPattern with ⟨suit, start⟩` は、順子パターンからスート `suit` と開始位置 `start` を取り出している。

`rcases proof with firstPattern | secondPattern`は、証拠が表す2つの可能性に分け、それぞれのパターンで
別の証明目標を作る。`MentsuPartition.all_mentsu`では、リストの要素が先頭と等しい場合を`rfl`、
末尾に含まれる場合を`restMember`として扱う。

### obtain

`obtain ⟨...⟩ := proof` は、存在や複数の部品を持つ証拠を分解し、中身に名前を付ける。
`pair_of_mem_pairChunkCandidates` では、候補が `map` 元のどの牌種から作られたかを取り出す。

### rename_i

`rename_i name ...` は、Leanが自動的に導入した無名または内部名の変数へ、証明中で使う名前を付ける。
`mem_decomposeMentsu_iff`では、分解証拠を場合分けした後に現れる残り牌列と残り面子列を命名する。

### simp

`simp` は、定義を展開したり、既知の事実で式を書き換えたりして、目標を単純な形にするタクティクである。
`simp only [all, List.mem_append, List.mem_flatMap]` のように `only` を付けると、角括弧 `[...]` に並べた
定義や定理だけを使う。

`simp [all]` のように `only` を付けない場合は、角括弧内の指定に加えて、Leanが標準的に知っている単純化規則も使う。

角括弧には定義や定理だけでなく、`simp [inductionHypothesis]` のように手元の等式も指定できる。
この場合、`simp` は帰納法の仮定を現在の目標の書き換え規則として使う。

`simp [tiles, Shuntsu.tiles] at honor_mem` のように `at` を付けると、現在の目標ではなく、手元にある仮定
`honor_mem` を単純化する。

### simp_all

`simp_all` は、現在の目標だけでなく、手元の仮定も使って単純化するタクティクである。
`expectedKind_iff` では、`Classifies` の各場合から得られる仮定を使い、`expectedKind` が対応する分類名を返すことを確認している。

### simpa と using

`simpa [...] using proof` は、手元の証拠 `proof` の型と現在の目標を単純化し、同じ形になることを確認する。
`canonicalize_eq_of_perm` では、`mergeSort` が整列済みであるという一般定理を、`canonicalize` と `orderLE` の
定義を展開して現在の目標へ合わせる。

### `List.mem_flatten`

`List.mem_flatten`は、値が`List.flatten xss`に含まれることを、その値を含む内側のリストが
`xss`に存在することとして読み替える。`mem_decomposeMentsu_iff`では、全候補の分解結果をまとめた列から、
実際に対象の分解を生成した候補の枝を取り出す。

### subst

`subst x`は、手元にある`x = value`または`value = x`という等式を使い、証明中の`x`を`value`へ置き換える。
置き換え後、その等式と変数`x`は不要になる。

### rw

`rw [proof]`は、等式`proof`を使って現在の目標や仮定を書き換える。
`mem_decomposeMentsu_iff`では、`removeTiles`の計算結果を成功時の`some remaining`へ書き換える。

`rw [← proof]` の矢印 `←` は、等式を右辺から左辺への向きで使う。`at hypothesis` を付けると、
目標ではなく指定した仮定の型を書き換える。`WinningPartition.of_perm` では、残り牌列の長さの等式を
逆向きに使い、手元の面子分解証拠の型を新しい残り牌列に必要な形へ揃える。

### `▸`

`equality ▸ proof`は、等式に沿って`proof`の型を書き換える項形式の記法である。
`mem_decomposeMentsu_iff`では、`map`から得た完成面子列の等式に合わせて、構築した分解証拠の結論を書き換える。

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

### omega

`omega` は、自然数や整数の加減算、不等式、等式からなる算術的な目標を解くタクティクである。
`canonicalize_eq_of_perm` では、2つのキーが互いに以下なら等しいことを導く。

### `.trans` と `.symm`

`proof.trans next` は「AとBの間に関係がある」と「BとCの間に関係がある」をつなぎ、
「AとCの間にも関係がある」という証拠を作る。`proof.symm` はその関係の向きを逆にする。
`canonicalize_eq_of_perm` では、整列前後の順列関係と、仮定で与えられた2入力間の順列関係をつなぐ。

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

### `∀`

`∀ x, P x`は、任意の値`x`について条件`P x`が成り立つことを表す。
`∀ chunk ∈ chunks, P chunk`は、リスト`chunks`に含まれるすべての`chunk`について`P chunk`が成り立つ、
という意味である。

### `List.mem_cons`

`List.mem_cons`は、値`x`が`first :: rest`に含まれることを、`x = first`または`x ∈ rest`として読み替える。
`MentsuPartition.all_mentsu`では、分解列の要素が先頭か末尾のどちらに由来するかを分けるために使う。

### `∃`

`∃ x, P x` は、条件 `P` を満たす値 `x` が少なくとも1つ存在することを表す。
`pair_of_mem_pairChunkCandidates` の結論は、候補の完成部品を作った雀頭が存在することを述べる。

### `↔`

`P ↔ Q` は、命題 `P` と命題 `Q` が同値であることを表す。
`expectedKind_iff` では、参照実装 `expectedKind profiles = some kind` と、宣言的仕様 `Classifies profiles kind` が同値であることを示す。

### 健全性と完全性

実行器と仕様の一致を2方向で述べるとき、健全性は「実行器が返した結果は仕様を満たす」、
完全性は「仕様を満たす結果を実行器が取りこぼさない」という保証を指す。
`mem_decomposeMentsu_iff`では、左から右が健全性、右から左が完全性に対応する。

### `¬`

`¬P` は、命題 `P` が成り立たない、という意味である。
`¬candidate.IsShuntsu` は、その完成面子候補が順子ではないことを表す。

### `∉`

`x ∉ xs` は、`x` がリストや集合 `xs` に含まれない、という意味である。
`take_snd_not_mem` の主張は、取り出した牌が残りの集合にはもう含まれないことを表す。
