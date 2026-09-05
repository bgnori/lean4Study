# Obsolete用語

この文書は、コードから削除した概念・用語・APIと、置き換え先または削除理由を記録する。
後継がないものも、かつて何を表していたかを明示して残す。
通常の読者は読む必要がない。現在の用語は [domain-vocabulary.md](domain-vocabulary.md) を参照する。

## 和了構成部品まわり

### `TileChunk`

置き換え先: `WinningComponent`

旧 `TileChunk := Toitsu ⊕ MentsuCandidate` は、通常形の和了分割に現れる
「雀頭または完成面子候補」を表していた。一方、[Mahjong/Basic.lean](../Mahjong/Basic.lean) の
旧 `Chunk` は物理牌の有限集合であり、同じ `Chunk` 語幹が異なる概念を指していた。

現在は、通常形の和了分割を構成する部品を `WinningComponent` と呼ぶ。
物理牌抽出経路の廃止に伴い、`Chunk` 自体も削除した。

### 「完成部品」

置き換え先: 「和了構成部品」

「完成部品」は、完成面子そのもの、待ち牌除去後の観測成分、旧物理牌集合 `Chunk` との関係が曖昧だったため使わない。
現在はコード上の `WinningComponent` と日本語の「和了構成部品」を一対一に対応させる。

### `winningChunks` と周辺名

置き換え先:

- `WaitCompletion.winningChunks` → `WaitCompletion.winningComponents`
- `pairChunkCandidates` → `pairComponentCandidates`
- `mentsuChunkCandidates` → `mentsuComponentCandidates`
- `WinningShape.chunk` → `WinningShape.component`
- `WinningShape.chunks` → `WinningShape.components`

和了構成部品を指す補助変数・定理名の `chunk(s)` も `component(s)` に寄せた。
物理牌集合 `Chunk` も後に削除され、現行コードには `Chunk` は残らない。

## 物理牌抽出モデル

### `Chunk` と `Chunk.take*`

置き換え先: なし

`Chunk` は、空でない物理牌集合を表していた。`Chunk.take`、`Chunk.takeTileFrom`、
`Chunk.takeTilesFrom`、`Chunk.takeTiles` は、その集合から指定した牌種に対応する物理牌を
取り出す処理だった。

待ち探索と待ち分解は牌種 `Tile` の列を直接扱っており、この物理牌抽出経路を使用していなかったため削除した。

### `HasTilePattern` と各 `take`

置き換え先: 各型の `tiles`

`HasTilePattern` は、牌パターンから牌種列を得て `Chunk` の共通抽出処理へ渡す型クラスだった。
物理牌抽出経路とともに、`HasTilePattern.take`、各型のインスタンス、`Toitsu.take`、
`Shuntsu.take`、`MentsuCandidate.take`、`WinningComponent` のインスタンスを削除した。
牌パターンを構成する牌種列が必要な場合は、それぞれの型に残る `tiles` を直接使う。

## 独立した待ちパターン型

### `RyanmenStart` と `ryanmenStartCount`

置き換え先: `ShuntsuStart` と `componentKindAfterRemovingWait`

`RyanmenStart` は両面ターツの開始位置を表し、`lowerRank` と `upperRank` を提供していた。
現行の待ち分解では、完成順子の `ShuntsuStart` と待ち牌の位置から両面かどうかを判定するため、
独立した開始位置型とその要素数を削除した。

### `Taatsu`

置き換え先: `WaitComponent`

`Taatsu` は両面・嵌張・辺張を独立した牌パターンとして表していた。
現行コードでは `WaitCompletion` の和了構成部品から待ち牌を除いて `WaitComponent` を作り、
その `kind` でこれらを区別するため、別系統の表現だった `Taatsu` を削除した。

### `Tanki`

置き換え先: `WaitComponent`

`Tanki` は単騎待ちの核になる1枚を独立した牌パターンとして表し、`all`、`Matches`、`take` を
提供していた。現行コードでは対子から待ち牌を除いた `WaitComponent` の `kind = .tanki` として
表すため、独立した型と付随APIを削除した。

## 待ち分解の便宜API

### `waitDecompositionCodesWithWait`

置き換え先: `waitDecompositionCodeEntries`

`WaitDecompositionCodeEntry` を `(コード, 待ち牌)` のタプルへ写すだけの別表現だった。
名前付きフィールドを持つ元の構造体より情報の意味が分かりにくくなるため削除した。

### `findWaitDecompositions` などの探索ラッパー

置き換え先: `WaitCompletionFinder.findWaitCompletions` と各変換関数の合成

次の関数は、牌列に `findWaitCompletions` を適用してから変換関数へ渡すだけのラッパーだったため削除した。

- `findWaitDecompositions`
- `findWaitCoreExtractions`
- `findWaitKindDecompositions`
- `findWaitDecompositionCodeEntries`
- `findWaitDecompositionCodesWithWait`

`findWaitCores` と `findWaitDecompositionCodes` は、現行コードで牌列から直接使う入口として残している。

## Reading系の旧語彙

`Reading` は、麻雀一般の「相手の待ちを推測する待ち読み」と衝突し、さらに観測結果と生成証人という
異なる役割を同じ語で表していたため廃止した。

置き換え先:

- `WaitReadingCode` → `WaitDecompositionCode`
- `ConcreteWaitReadingComponent` → `WaitComponent`
- `WaitReadingComponentKind` → `WaitComponentKind`
- `ConcreteWaitReading` → `WaitDecomposition`
- `AbstractWaitReading` → `WaitKindDecomposition`
- `IrreducibleWaitReading` → `WaitCoreExtraction`
- `WaitReadingCodeEntry` → `WaitDecompositionCodeEntry`
- `DirectWaitReading` → `DirectWaitGeneration`
- `DirectWaitReading.Reading` → `DirectWaitGeneration.WaitDerivation`
- `HasNobetanReading` → `ContainsNobetan`

`WinningComponent` は待ち牌を除く前の和了構成部品、`WaitComponent` はそこから待ち牌を除いた結果、
または除去せず完成形のまま保持した部品である。両者は別の処理段階を表す。