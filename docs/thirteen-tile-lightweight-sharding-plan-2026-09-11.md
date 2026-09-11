# 13枚形レポート生成：軽量シャード化案 2026-09-11

## 背景と動機

前の完全なシャード化設計は、導出ファイル・マニフェスト・`.done` マーカーなど複雑な状態管理が必要でした。
一方、チェックポイント方式は実装は簡単（100～150行）ですが、メモリ内のハッシュマップが生成終了まで
増え続けるため、OOMリスク（8GBコンテナで最大8時間の計算が失敗）を根本的には解決しません。

本案は両者の中間：**粗いシャード分割（key % numShards）で、ピークメモリを事前に削減**しつつ、
**チェックポイントなみの実装シンプルさを保つ**折衷案です。

## 目標

1. **ピークメモリ削減**：シャード数 k に対して、ピークメモリを約 1/k に圧縮（同時保持件数が削減）
2. **実装コスト最小化**：完全シャード化（300～500行）より小さい（150～250行）
3. **安全性向上**：各シャードが独立に30分以内で完了する設定を目指す
4. **再開可能性**：シャード k が失敗しても、再実行すれば他のシャードの結果と統合可能

## 実装方針

### 1. シャード分割キー

牌多重集合キーの下位ビットで分割：

```lean
def shardIndex (tiles : List Tile) (numShards : Nat) : Nat :=
  tileMultisetKey tiles % numShards
```

- 分割は排他的（各牌姿はちょうど1シャードに属する）
- 異なるシャード間に重複なし

### 2. シャード数の選定

10枚形の実測から逆算：

- **実測値**：テンパイ形 3,431,439 件、実行時間 1043秒（17分23秒）
- **1件あたり**：0.30秒
- **目標時間**：30分以内で完全に完了

13枚形推定：

| シナリオ | テンパイ形数 | 1件コスト | 13枚形時間 | シャード数 k | 1シャード時間 |
|--------|------------|---------|----------|----------|-----------|
| 楽観的 | 50M | 0.30秒 | 4.2時間 | 8 | 31分 |
| 中心 | 67.5M | 0.30秒 | 5.6時間 | 10 | 34分 |
| 悲観的 | 85M | 0.35秒 | 8.3時間 | 14 | 35分 |

**推奨**：`numShards = 12`（中心値で30分以内、悲観的でも40分以内）

ピークメモリ削減：
$$
\text{ピークメモリ} \approx \frac{2.6 \text{ GB}}{12} \sim \frac{4.4 \text{ GB}}{12} \approx \text{0.22～0.37 GB}
$$

これはメモリの余裕が十分であり、複数シャードの並列処理や再実行も可能になります。

### 3. 処理フロー

```
Step 1: numShards = 12 に対して、shardIndex ∈ {0, 1, ..., 11}
Step 2: 各シャード i に対して処理を実行
        - 牌姿ごとのフォルダ: reports/thirteen-tile-shards/shard-{i}/
        - 出力ファイル: reports/thirteen-tile-shards/shard-{i}/result.txt
Step 3: 全シャード完了後、結果を統合
        - 最終ファイル: reports/thirteen-tile-direct-report.txt
```

### 4. 各シャード処理の実装

`MahjongComputations/ThirteenTile.lean` を改造：

```lean
structure ThirteenTileShardConfig where
  shardIndex : Nat
  numShards : Nat

def computeThirteenTileShard (config : ThirteenTileShardConfig) : IO ThirteenTileReport := do
  let result := canonicalWaitCompletionGroups 4
  let filtered := result.groups.filter fun group =>
    shardIndex (group.tiles) config.numShards == config.shardIndex
  -- filtered に対してレポート集計を行う
  ⟨...⟩
```

### 5. 最終マージ

各シャード結果ファイル（JSONL または テキスト）を順番に読み込んで、
グローバルな集計（テンパイ形総数、可約性グループなど）を再計算：

```lean
def mergeThirteenTileShards (numShards : Nat) : IO ThirteenTileReport := do
  let mut allGroups : List WaitDecompositionCodeGroup := []
  for i in [0 : numShards] do
    let filePath := s!"reports/thirteen-tile-shards/shard-{i}/result.txt"
    let shardResult ← loadThirteenTileShardResult filePath
    allGroups := allGroups ++ shardResult.groups
  -- 統計情報を再計算して最終レポートを生成
  formatThirteenTileReport allGroups
```

### 6. lakefileへの追加

```lean
-- thirteenTileReport の代わり、シャードごとのターゲットを追加
def thirteenTileShardTargets : List (Lean.Lake.BuildJob _) :=
  (List.range 12).map fun i =>
    { name := s!"thirteen-tile-report-shard-{i}"
      executable := "thirteen-tile-report-shard-gen"
      args := [s!"--shard={i}", s!"--num-shards=12", ...]
    }

-- 統合ターゲット
target "thirteen-tile-report" := do
  -- 全シャードの完了を待ち、マージを実行
  ...
```

## 実装コスト見積もり

| タスク | 行数 | 時間 |
|------|------|------|
| `ThirteenTile.lean` へのシャード引数追加 | 30 | 15分 |
| `canonicalWaitCompletionGroups` のフィルタリング版 | 20 | 10分 |
| マージ・統計再計算関数 | 60 | 30分 |
| `lakefile.lean` でシャード・統合ターゲット定義 | 40 | 20分 |
| テスト・検証（10枚形サンプル） | 50 | 1時間 |
| **合計** | **200** | **2時間15分** |

## 検証計画

### Phase 1: 10枚形での仕様確認（30分）

1. `TenTile.lean` を改造して `shardIndex` を追加
2. `numShards = 3` で試験的に10枚形を3シャードに分割
3. 各シャード結果が正確にマージできることを確認
4. マージ後の統計が単一実行と一致するか検証

### Phase 2: 13枚形での初回実行（5～8時間）

1. `numShards = 12` で 13枚形を 12 シャードに分割
2. 各シャード i を順番に実行（または手動で並列実行）
3. 最大実行時間が35分以内に収まることを確認
4. 最終マージで結果を統合

### Phase 3: 安全な中断再開（必要な場合のみ）

1. シャード k が途中で失敗した場合、そのシャードだけ再実行
2. 他のシャード結果と統合して最終レポートを生成

## 既存実装への影響

- `MahjongComputations/Common.lean`：影響なし（`canonicalWaitCompletionGroups` は不変）
- `MahjongComputations/FourTile.lean`, `SevenTile.lean`：影響なし
- `MahjongComputations/TenTile.lean`, `ThirteenTile.lean`：シャード対応版を別実装
  （元のモノリシック版は残す、必要に応じて）

## 懸念点と対策

| 懸念 | 対策 |
|-----|------|
| 12シャードを順番に実行すると合計時間が長い | 手動で複数ターミナルで並列実行可能 |
| 1シャード失敗時の復旧が手作業になる | シャード i の再実行スクリプトを用意 |
| 統計再計算の誤り | 10枚形で 3 シャード × 2 回実行して検証 |
| シャードサイズのばらつき | `key % numShards` は均等分布を仮定（後で測定） |

## 次のステップ

1. 本計画をコードレビュー
2. `TenTile.lean` で軽量シャード化プロトタイプを実装
3. 10枚形で 3 シャード版を実行・検証
4. 問題なければ `ThirteenTile.lean` で `numShards = 12` 版を実装
5. 13枚形レポートを生成
