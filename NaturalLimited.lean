import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
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

/-- `Rank` は `Fin 13` の別名なので、`0` から `12` までのリテラルを書けるようにする。 -/
instance (n : Nat) [OfNat (Fin 13) n] : OfNat Rank n where
  ofNat := (OfNat.ofNat n : Fin 13)

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

/-!
## ポーカーの役判定

以降では、上で定義した `Card` を使って、5枚の手札からポーカーの役を判定する。

Lean では「5枚である」という条件を実行時チェックにせず、`Fin 5 -> Card` という型で
表している。`Fin 5` は添字 `0, 1, 2, 3, 4` だけを持つので、この関数は必ず5枚ぶんの
カードを返す。
-/

/-- ちょうど5枚のカードからなる手札。 -/
def Hand := Fin 5 -> Card

/-- ポーカーの役。下に行くほど強い役として並べている。 -/
inductive PokerHand
  | highCard
  | onePair
  | twoPair
  | threeOfAKind
  | straight
  | flush
  | fullHouse
  | fourOfAKind
  | straightFlush
  deriving BEq, DecidableEq, Repr

/-- テストや例を書くためのカード生成ヘルパー。 -/
def mkCard (suit : Suit) (rank : Rank) : Card :=
  { suit := suit, rank := rank }

/-- 5枚のカードから `Hand` を作るヘルパー。 -/
def mkHand (c0 c1 c2 c3 c4 : Card) : Hand
  | ⟨0, _⟩ => c0
  | ⟨1, _⟩ => c1
  | ⟨2, _⟩ => c2
  | ⟨3, _⟩ => c3
  | ⟨4, _⟩ => c4

/-- 手札の中で指定したランクが何枚あるかを数える。 -/
def rankCount (hand : Hand) (rank : Rank) : Nat :=
  ((Finset.univ : Finset (Fin 5)).filter fun i => (hand i).rank = rank).card

/-- 「ちょうど `n` 枚あるランク」が何種類あるかを数える。 -/
def rankGroupCount (hand : Hand) (n : Nat) : Nat :=
  ((Finset.univ : Finset Rank).filter fun rank => rankCount hand rank = n).card

/-!
### 型から得られる不変条件

以下は特定の手札に対するテストではなく、任意の `hand : Hand` について成り立つ定理である。
`Hand` の添字が `Fin 5` なので、各ランクの枚数は5を超えず、ランクのグループ数は
`Rank = Fin 13` の13種類を超えない。また、0番目のカードが必ず存在するため、少なくとも
1つのランクは必ず手札に含まれる。実装を変更しても、これらの性質を壊す変更は型検査で
検出される。
-/

/-- 任意のランクは、5枚の手札の中に高々5枚しか現れない。 -/
theorem rankCount_le_five (hand : Hand) (rank : Rank) : rankCount hand rank <= 5 := by
  unfold rankCount
  calc
    ((Finset.univ : Finset (Fin 5)).filter fun i => (hand i).rank = rank).card <=
        (Finset.univ : Finset (Fin 5)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 5 := by decide

/-- ちょうど同じ枚数のランクは、全13ランクを超えて存在しない。 -/
theorem rankGroupCount_le_thirteen (hand : Hand) (n : Nat) : rankGroupCount hand n <= 13 := by
  unfold rankGroupCount
  calc
    ((Finset.univ : Finset Rank).filter fun rank => rankCount hand rank = n).card <=
        (Finset.univ : Finset Rank).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 13 := by decide

/-- 任意の手札には、少なくとも1回現れるランクがある。 -/
theorem exists_rank_with_positive_count (hand : Hand) : ∃ rank, 0 < rankCount hand rank := by
  refine ⟨(hand 0).rank, ?_⟩
  unfold rankCount
  apply Finset.card_pos.mpr
  refine ⟨0, ?_⟩
  simp

/-- 指定した自然数値のランクが手札に含まれるかを判定する。 -/
def hasRankValue (hand : Hand) (rankValue : Nat) : Bool :=
  decide <| 0 < ((Finset.univ : Finset (Fin 5)).filter fun i => (hand i).rank.val = rankValue).card

/-- Ace を `0` として扱う Broadway ストレートかどうかを判定する。 -/
def isBroadwayStraight (hand : Hand) : Bool :=
  hasRankValue hand 0 &&
  hasRankValue hand 9 &&
  hasRankValue hand 10 &&
  hasRankValue hand 11 &&
  hasRankValue hand 12

/--
5枚が同じスートなら `true`。

基準には0番目のカードを使う。`Hand` は必ず5枚なので、このカードは常に存在する。
-/
def isFlush (hand : Hand) : Bool :=
  decide <|
    ((Finset.univ : Finset (Fin 5)).filter fun i =>
      (hand i).suit = (hand ⟨0, by decide⟩).suit).card = 5

/--
5枚のランクが連続していれば `true`。

ここでは `Rank` を `Fin 13` の値 `0, 1, ..., 12` として扱う。通常の連続する
5ランクに加えて、`0` を Ace と見た `0, 9, 10, 11, 12` も Broadway
ストレートとして扱う。
-/
def isStraight (hand : Hand) : Bool :=
  isBroadwayStraight hand ||
    (decide <| 0 < ((Finset.range 9).filter fun start =>
      ((Finset.range 5).filter fun offset => hasRankValue hand (start + offset) = true).card = 5).card)

/-- 5枚の手札からポーカーの役を判定する。 -/
def classifyHand (hand : Hand) : PokerHand :=
  if isStraight hand && isFlush hand then
    PokerHand.straightFlush
  else if rankGroupCount hand 4 > 0 then
    PokerHand.fourOfAKind
  else if rankGroupCount hand 3 > 0 && rankGroupCount hand 2 > 0 then
    PokerHand.fullHouse
  else if isFlush hand then
    PokerHand.flush
  else if isStraight hand then
    PokerHand.straight
  else if rankGroupCount hand 3 > 0 then
    PokerHand.threeOfAKind
  else if rankGroupCount hand 2 = 2 then
    PokerHand.twoPair
  else if rankGroupCount hand 2 = 1 then
    PokerHand.onePair
  else
    PokerHand.highCard

/-!
## テスト

Lean では、値を表示するだけの `#eval` よりも、期待する性質を `example` として
書いて型検査に通す形がよく使われる。下の各 `example` は、役判定の結果が期待値と
一致することを Lean に証明させている。
-/

example : classifyHand (mkHand
    (mkCard .spade 0)
    (mkCard .spade 1)
    (mkCard .spade 2)
    (mkCard .spade 3)
    (mkCard .spade 4)) = PokerHand.straightFlush := by
  native_decide

example : classifyHand (mkHand
    (mkCard .spade 7)
    (mkCard .heart 7)
    (mkCard .diamond 7)
    (mkCard .club 7)
    (mkCard .spade 2)) = PokerHand.fourOfAKind := by
  native_decide

example : classifyHand (mkHand
    (mkCard .spade 10)
    (mkCard .heart 10)
    (mkCard .diamond 10)
    (mkCard .club 3)
    (mkCard .spade 3)) = PokerHand.fullHouse := by
  native_decide

example : classifyHand (mkHand
    (mkCard .heart 0)
    (mkCard .heart 2)
    (mkCard .heart 5)
    (mkCard .heart 9)
    (mkCard .heart 12)) = PokerHand.flush := by
  native_decide

example : classifyHand (mkHand
    (mkCard .spade 8)
    (mkCard .heart 9)
    (mkCard .diamond 10)
    (mkCard .club 11)
    (mkCard .spade 12)) = PokerHand.straight := by
  native_decide

example : classifyHand (mkHand
    (mkCard .spade 4)
    (mkCard .heart 4)
    (mkCard .diamond 4)
    (mkCard .club 8)
    (mkCard .spade 12)) = PokerHand.threeOfAKind := by
  native_decide

example : classifyHand (mkHand
    (mkCard .spade 1)
    (mkCard .heart 1)
    (mkCard .diamond 6)
    (mkCard .club 6)
    (mkCard .spade 11)) = PokerHand.twoPair := by
  native_decide

example : classifyHand (mkHand
    (mkCard .spade 5)
    (mkCard .heart 5)
    (mkCard .diamond 2)
    (mkCard .club 9)
    (mkCard .spade 12)) = PokerHand.onePair := by
  native_decide

example : classifyHand (mkHand
    (mkCard .spade 0)
    (mkCard .heart 2)
    (mkCard .diamond 5)
    (mkCard .club 9)
    (mkCard .spade 12)) = PokerHand.highCard := by
  native_decide

example : classifyHand (mkHand
    (mkCard .spade 0)
    (mkCard .spade 9)
    (mkCard .spade 11)
    (mkCard .spade 12)
    (mkCard .spade 10)) = PokerHand.straightFlush := by
  native_decide

/-!
## テキサスホールデムの勝敗判定

テキサスホールデムでは、各プレイヤーの2枚のホールカードと5枚の共有カード、
合計7枚から最も強い5枚を選ぶ。ここでは7枚から作れる21通りの5枚手札をすべて
評価し、その最大値をそのプレイヤーの強さとする。
-/

/-- 2枚のホールカード。 -/
def HoleCards := Fin 2 -> Card

/-- 5枚の共有カード。 -/
def Board := Fin 5 -> Card

/-- 評価用の7枚カード。 -/
def SevenCards := Fin 7 -> Card

/-- 2枚のホールカードを作るヘルパー。 -/
def mkHoleCards (c0 c1 : Card) : HoleCards
  | ⟨0, _⟩ => c0
  | ⟨1, _⟩ => c1

/-- 5枚の共有カードを作るヘルパー。 -/
def mkBoard (c0 c1 c2 c3 c4 : Card) : Board :=
  mkHand c0 c1 c2 c3 c4

/-- `Rank` の値を比較用の強さに変換する。Ace である `0` を最強として扱う。 -/
def rankStrengthFromValue (rankValue : Nat) : Nat :=
  if rankValue = 0 then 12 else rankValue - 1

/-- 比較用の強い順のランク値。 -/
def rankValuesHighToLow : List Nat :=
  [0, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]

/-- カード集合の中で指定したランクが何枚あるかを数える。 -/
def rankCountIn (cards : Finset Card) (rank : Rank) : Nat :=
  (cards.filter fun card => card.rank = rank).card

/-- カード集合の中で指定したランク値が何枚あるかを数える。 -/
def rankCountValue (cards : Finset Card) (rankValue : Nat) : Nat :=
  (cards.filter fun card => card.rank.val = rankValue).card

/-- 「ちょうど `n` 枚あるランク」が何種類あるかを数える。 -/
def rankGroupCountIn (cards : Finset Card) (n : Nat) : Nat :=
  ((Finset.univ : Finset Rank).filter fun rank => rankCountIn cards rank = n).card

/-- 指定した自然数値のランクがカード集合に含まれるかを判定する。 -/
def hasRankValueIn (cards : Finset Card) (rankValue : Nat) : Bool :=
  decide <| 0 < rankCountValue cards rankValue

/-- Ace を `0` として扱う Broadway ストレートかどうかをカード集合で判定する。 -/
def isBroadwayStraightIn (cards : Finset Card) : Bool :=
  hasRankValueIn cards 0 &&
  hasRankValueIn cards 9 &&
  hasRankValueIn cards 10 &&
  hasRankValueIn cards 11 &&
  hasRankValueIn cards 12

/-- カード集合がフラッシュかどうかを判定する。 -/
def isFlushIn (cards : Finset Card) : Bool :=
  decide <| 0 < ((Finset.univ : Finset Suit).filter fun suit =>
    (cards.filter fun card => card.suit = suit).card = 5).card

/-- 通常の連続するストレートが `start` から始まるかどうか。 -/
def isNormalStraightFrom (cards : Finset Card) (start : Nat) : Bool :=
  decide <|
    ((Finset.range 5).filter fun offset =>
      hasRankValueIn cards (start + offset) = true).card = 5

/-- カード集合がストレートかどうかを判定する。 -/
def isStraightIn (cards : Finset Card) : Bool :=
  isBroadwayStraightIn cards ||
    (decide <| 0 < ((Finset.range 9).filter fun start =>
      isNormalStraightFrom cards start = true).card)

/-- 5枚のカード集合からポーカーの役を判定する。 -/
def classifyCardSet (cards : Finset Card) : PokerHand :=
  if isStraightIn cards && isFlushIn cards then
    PokerHand.straightFlush
  else if rankGroupCountIn cards 4 > 0 then
    PokerHand.fourOfAKind
  else if rankGroupCountIn cards 3 > 0 && rankGroupCountIn cards 2 > 0 then
    PokerHand.fullHouse
  else if isFlushIn cards then
    PokerHand.flush
  else if isStraightIn cards then
    PokerHand.straight
  else if rankGroupCountIn cards 3 > 0 then
    PokerHand.threeOfAKind
  else if rankGroupCountIn cards 2 = 2 then
    PokerHand.twoPair
  else if rankGroupCountIn cards 2 = 1 then
    PokerHand.onePair
  else
    PokerHand.highCard

/-- ちょうど `count` 枚あるランクを、強い順の比較値として返す。 -/
def rankStrengthsWithCount (cards : Finset Card) (count : Nat) : List Nat :=
  (rankValuesHighToLow.filter fun rankValue => decide <| rankCountValue cards rankValue = count).map
    rankStrengthFromValue

/-- ストレートの最上位ランクを比較用の値として返す。 -/
def straightHighStrength (cards : Finset Card) : Nat :=
  if isBroadwayStraightIn cards then
    12
  else
    (([8, 7, 6, 5, 4, 3, 2, 1, 0] : List Nat).filter fun start =>
      isNormalStraightFrom cards start).foldl
        (fun best start => max best (rankStrengthFromValue (start + 4))) 0

/-- 同じ役の中で比較するためのランク列。 -/
def cardSetTieBreakRanks (cards : Finset Card) : List Nat :=
  match classifyCardSet cards with
  | PokerHand.straightFlush => [straightHighStrength cards]
  | PokerHand.fourOfAKind => rankStrengthsWithCount cards 4 ++ rankStrengthsWithCount cards 1
  | PokerHand.fullHouse => rankStrengthsWithCount cards 3 ++ rankStrengthsWithCount cards 2
  | PokerHand.flush => rankStrengthsWithCount cards 1
  | PokerHand.straight => [straightHighStrength cards]
  | PokerHand.threeOfAKind => rankStrengthsWithCount cards 3 ++ rankStrengthsWithCount cards 1
  | PokerHand.twoPair => rankStrengthsWithCount cards 2 ++ rankStrengthsWithCount cards 1
  | PokerHand.onePair => rankStrengthsWithCount cards 2 ++ rankStrengthsWithCount cards 1
  | PokerHand.highCard => rankStrengthsWithCount cards 1

/-- 役の強さを数値にする。大きいほど強い。 -/
def pokerHandCategoryScore : PokerHand -> Nat
  | PokerHand.highCard => 0
  | PokerHand.onePair => 1
  | PokerHand.twoPair => 2
  | PokerHand.threeOfAKind => 3
  | PokerHand.straight => 4
  | PokerHand.flush => 5
  | PokerHand.fullHouse => 6
  | PokerHand.fourOfAKind => 7
  | PokerHand.straightFlush => 8

/-- ランク列を辞書式比較できる数値に変換する。 -/
def encodeRankList : Nat -> List Nat -> Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | remaining + 1, rankStrength :: rest =>
      rankStrength * 13 ^ remaining + encodeRankList remaining rest

/-- 5枚カード集合の比較用スコア。大きいほど強い。 -/
def cardSetScore (cards : Finset Card) : Nat :=
  pokerHandCategoryScore (classifyCardSet cards) * 13 ^ 5 +
    encodeRankList 5 (cardSetTieBreakRanks cards)

/-- ホールカードと共有カードを、重複のないカード集合としてまとめる。 -/
def holdemCardSet (holeCards : HoleCards) (board : Board) : Finset Card :=
  ({holeCards 0, holeCards 1} : Finset Card) ∪
    ({board 0, board 1, board 2, board 3, board 4} : Finset Card)

/-- カード集合から作れる5枚カード集合をすべて列挙する。 -/
def allFiveCardSets (cards : Finset Card) : Finset (Finset Card) :=
  cards.powersetCard 5

/-- 7枚のカード集合からは、5枚カード集合が21通り作れる。 -/
theorem allFiveCardSets_card_of_card_eq_seven {cards : Finset Card} (h : cards.card = 7) :
    (allFiveCardSets cards).card = 21 := by
  unfold allFiveCardSets
  rw [Finset.card_powersetCard, h]
  decide

/-- テキサスホールデムで、あるプレイヤーが作れる最良の5枚手札のスコア。 -/
def bestHoldemScore (holeCards : HoleCards) (board : Board) : Nat :=
  (allFiveCardSets (holdemCardSet holeCards board)).sup cardSetScore

/-- 2人以上10人以下のテキサスホールデム卓。 -/
structure HoldemTable where
  playerCount : Nat
  minPlayers : 2 <= playerCount
  maxPlayers : playerCount <= 10
  holeCards : Fin playerCount -> HoleCards
  board : Board

/-- 卓上での指定プレイヤーのスコア。 -/
def holdemPlayerScore (table : HoldemTable) (player : Fin table.playerCount) : Nat :=
  bestHoldemScore (table.holeCards player) table.board

/-- 卓上の最高スコア。 -/
def holdemBestScore (table : HoldemTable) : Nat :=
  (Finset.univ : Finset (Fin table.playerCount)).sup fun player =>
    holdemPlayerScore table player

/-- 勝者の集合。同点の場合は複数プレイヤーを返す。 -/
def holdemWinners (table : HoldemTable) : Finset (Fin table.playerCount) :=
  (Finset.univ : Finset (Fin table.playerCount)).filter fun player =>
    holdemPlayerScore table player = holdemBestScore table

/-- 2人卓を作るヘルパー。 -/
def mkTwoPlayerTable (player0 player1 : HoleCards) (board : Board) : HoldemTable where
  playerCount := 2
  minPlayers := by decide
  maxPlayers := by decide
  holeCards
    | ⟨0, _⟩ => player0
    | ⟨1, _⟩ => player1
  board := board

/-- 3人卓を作るヘルパー。 -/
def mkThreePlayerTable (player0 player1 player2 : HoleCards) (board : Board) : HoldemTable where
  playerCount := 3
  minPlayers := by decide
  maxPlayers := by decide
  holeCards
    | ⟨0, _⟩ => player0
    | ⟨1, _⟩ => player1
    | ⟨2, _⟩ => player2
  board := board

/-!
## テキサスホールデムのテスト
-/

example : holdemWinners (mkTwoPlayerTable
    (mkHoleCards (mkCard .spade 8) (mkCard .heart 0))
    (mkHoleCards (mkCard .diamond 2) (mkCard .club 2))
    (mkBoard
      (mkCard .heart 4)
      (mkCard .club 5)
      (mkCard .diamond 6)
      (mkCard .spade 7)
      (mkCard .club 12))) = ({(0 : Fin 2)} : Finset (Fin 2)) := by
  native_decide

example : holdemWinners (mkTwoPlayerTable
    (mkHoleCards (mkCard .diamond 3) (mkCard .club 6))
    (mkHoleCards (mkCard .heart 8) (mkCard .diamond 12))
    (mkBoard
      (mkCard .spade 0)
      (mkCard .spade 9)
      (mkCard .spade 10)
      (mkCard .spade 11)
      (mkCard .spade 12))) = (Finset.univ : Finset (Fin 2)) := by
  native_decide

example : holdemWinners (mkTwoPlayerTable
    (mkHoleCards (mkCard .spade 0) (mkCard .heart 12))
    (mkHoleCards (mkCard .diamond 0) (mkCard .club 11))
    (mkBoard
      (mkCard .spade 5)
      (mkCard .heart 5)
      (mkCard .diamond 2)
      (mkCard .club 7)
      (mkCard .spade 9))) = ({(0 : Fin 2)} : Finset (Fin 2)) := by
  native_decide

example : holdemWinners (mkThreePlayerTable
    (mkHoleCards (mkCard .spade 3) (mkCard .club 8))
    (mkHoleCards (mkCard .diamond 1) (mkCard .club 11))
    (mkHoleCards (mkCard .heart 0) (mkCard .heart 12))
    (mkBoard
      (mkCard .heart 1)
      (mkCard .heart 4)
      (mkCard .heart 8)
      (mkCard .club 6)
      (mkCard .diamond 10))) = ({(2 : Fin 3)} : Finset (Fin 3)) := by
  native_decide
