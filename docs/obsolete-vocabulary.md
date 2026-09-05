# Obsolete用語

この文書は、現在の読書導線から外した旧用語と、その置き換え先だけを記録する。
通常の読者は読む必要がない。現在の用語は [domain-vocabulary.md](domain-vocabulary.md) を参照する。

## 和了構成部品まわり

### `TileChunk`

置き換え先: `WinningComponent`

旧 `TileChunk := Toitsu ⊕ MentsuCandidate` は、通常形の和了分割に現れる
「雀頭または完成面子候補」を表していた。一方、[Mahjong/Basic.lean](../Mahjong/Basic.lean) の
`Chunk` は物理牌の有限集合であり、同じ `Chunk` 語幹が異なる概念を指していた。

現在は、通常形の和了分割を構成する部品を `WinningComponent` と呼ぶ。
物理牌集合 `Chunk` とその局所変数名 `chunk` は別概念として維持する。

### 「完成部品」

置き換え先: 「和了構成部品」

「完成部品」は、完成面子そのもの、待ち牌除去後の観測成分、物理牌集合 `Chunk` との関係が曖昧だったため使わない。
現在はコード上の `WinningComponent` と日本語の「和了構成部品」を一対一に対応させる。

### `winningChunks` と周辺名

置き換え先:

- `WaitCompletion.winningChunks` → `WaitCompletion.winningComponents`
- `pairChunkCandidates` → `pairComponentCandidates`
- `mentsuChunkCandidates` → `mentsuComponentCandidates`
- `WinningShape.chunk` → `WinningShape.component`
- `WinningShape.chunks` → `WinningShape.components`

和了構成部品を指す補助変数・定理名の `chunk(s)` も `component(s)` に寄せた。
コード検索で残る `Chunk` は、物理牌集合を指すものに限定する。

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