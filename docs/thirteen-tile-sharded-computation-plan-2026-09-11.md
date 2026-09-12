# 13枚形の分割計算案

作成日: 2026-09-11

## 背景

13枚形レポートは `canonicalWaitCompletionGroups 4` を使って4面子の正準導出を生成し、
牌姿ごとに完成情報をまとめた後、可約性を判定する。10枚形は次の実測で完走した。

- 旧単一プロセス版の実時間: 17分23.521秒
- 外部bucket・4 worker版の実時間: 6分50.130秒（約2.54倍高速化）
- `enumeratedDerivations`: 5,536,779
- `tenpaiReports`: 3,431,439
- wait-core cache: 3,701,891 hits / 295,762 misses
- 4 worker版でも上記件数とreducible 3,416,313、irreducible 15,126、既約code group 199が一致
- 実行中のCPU使用率: 約180%前後

13枚形は10枚形より導出数、牌姿グループ数、キャッシュサイズが増えるため、単一プロセスで
最後までメモリ上に保持する方式は避ける。計算を分割し、中間結果と完了状態をディスクに保存する。
これにより、途中停止やプロセス終了があっても、完了済み部分を失わずに再開できる。

## 基本方針

計算を次の2段階に分離する。

1. 正準導出を生成し、最終的な牌姿キーに応じた shard ファイルへ書き出す。
2. shard ごとに完成情報を集約し、可約性判定とレポート集計を行う。

重要なのは、面子組合せの範囲だけで最終結果を分割しないことである。同じ牌姿へ射影される
導出が複数の面子組合せに由来するため、面子範囲だけで分類すると同一牌姿の completion が
別々のワーカーへ分散する。まず `tileMultisetKey tiles % shardCount` で振り分け、同じ牌姿の
全 completion が必ず同じ shard に入るようにする。

この二段構成は10枚形で実装・完走済みである。現在の実装は64個の固定幅binary bucket、
雀頭牌単位の並列生成、bucket単位の並列分類、および全worker共有のsingle-flight cacheを使う。
13枚形ではこの経路を基礎にしつつ、チェックポイントとcacheのメモリ上限を追加する。

## 第1段階: 導出の外部化

各正準導出から、少なくとも次のレコードを作る。

```text
tileMultisetKey\tencodedCompletion
```

牌姿そのものはキーから復元できる場合でも、デバッグと再現性のため、初期実装では牌姿または
復元可能な正規化表現も保存する。Lean の構造体をそのまま `repr` で保存するのではなく、
整数列などの明示的なバイナリまたはタブ区切り形式を定義する。形式にはバージョン番号を持たせる。

現在の実装では、bucketごとにmutexで保護したbuffered writerを一つ持ち、全生成workerが
`tileMultisetKey`に対応するwriterへ追記する。

```text
.lake/build/thirteen-tile-buckets/bucket-0.bin
.lake/build/thirteen-tile-buckets/bucket-1.bin
...
```

各ファイルはmagic、形式version、面子数、固定record幅を含むheaderを持つ。全writerのflushが
成功した後にだけ、生成全体の`generation.done`をatomic renameで確定する。

### 生成段階の再開

細かい生成範囲ごとのcheckpointは作らない。生成段階全体について次のmarkerだけを持つ。

```text
.lake/build/thirteen-tile-buckets/generation.done
```

markerには形式version、面子数、bucket数、導出数を保存する。markerと全bucketが存在し、設定が
一致する場合だけ生成を省略する。生成中断時にはmarkerがないため、次回はbucketをtruncateして
生成全体をやり直す。この粒度なら追加I/Oをほぼ増やさず、より重い分類だけを再試行できる。

## 第2段階: shard の集約と分類

各 shard を一つずつ処理する。

1. shard 内のレコードを `tileMultisetKey` でまとめる。
2. 同じ牌姿の completion を重複除去する。
3. `waitsFromCompletions` と wait decomposition code を計算する。
4. 可約性を判定する。
5. 件数、待ち種類数分布、既約コードグループを shard 集計へ加える。

shard 集約中も全牌姿をリストに保持しない。HashMap のメモリ上限を設け、上限を超える場合は、
レコードをソート済み runs に分割して外部マージする方式へ切り替える。最初から大規模な単一
HashMap を前提にしない。

## キャッシュの設計

現在のキャッシュは次の関数型である。

```text
remaining tileMultisetKey -> Option (List WaitCore)
```

この値は元牌姿ではなく除去後の牌姿だけに依存するため、bucket集約中に再利用できる。現在は
全分類workerで64 stripeのsingle-flight cacheを共有し、同じキーの同時計算も一度にまとめる。

cacheのdisk退避は採用しない。32-core Codespacesではまずmemory-only共有cacheで実測し、
メモリ不足が確認された場合だけentry上限や分類worker数の削減を検討する。append-only cache logは
ランダム参照とcompactのI/Oが計算時間を支配するおそれがあるため、先回りして導入しない。

## 集計結果の統合

各bucketはworker-local summaryへ畳み込み、最後にmemory上で統合する。

```text
handCount
reducibleCount
irreducibleCount
waitTileCountDistribution
irreducibleCodeGroups
cacheHits
cacheMisses
cacheEntries
```

最終統合では、hand count、可約・既約件数、待ち種類数分布を加算する。既約コードグループは
コード列をキーに再集約し、cache統計は共有cacheから一度だけ取得する。bucket別summaryはdiskへ
保存しない。

## チェックポイントと再開

永続化する完了状態は生成段階だけである。

```text
shard-000.data
shard-000.manifest
bucket-0.bin
bucket-1.bin
...
generation.done
`.done` は `.data` と manifest の checksum、レコード件数、プログラムバージョンを検証した後に
作成する。再開時は `.done` があり、検証に成功した shard をスキップする。壊れた、または形式が
`generation.done`は全bucketをflushした後に作る。再開時はmarkerの設定と全bucketの存在を確認し、
一致すれば生成を省略する。分類時には各bucketのheaderと固定record幅を検証する。分類途中で停止した
場合は分類を先頭からやり直すが、導出生成は繰り返さない。

最初から32分割で本番を開始しない。次の順序で検証する。

1. 10枚形を2分割し、分割前後で全件数、可約・既約件数、コードグループが一致することを確認する。
2. 10枚形で中断と再開を行い、完了 shard を再計算しないことを確認する。
3. 13枚形の小さい生成範囲を2分割または4分割し、1範囲あたりのレコード数、入力サイズ、
   cache miss 数、RSS、処理時間を測る。
4. 実測から8、16、32分割を選ぶ。

分割数はコア数ではなく、各 shard のメモリ上限とディスク帯域で決める。2コア環境なら同時実行は
通常1〜2プロセスにし、32コア環境でもI/Oが飽和するなら同時実行数を下げる。

### 32-core Codespacesでの初期設定

`.devcontainer/devcontainer.json`では最低要件を32 CPU、64 GB RAM、64 GB storageとし、
Docker側の`--cpus`・`--memory`制限は設定しない。Codespacesで32-core machineを選択した後、
次の値が期待通りか確認する。

```bash
nproc
cat /sys/fs/cgroup/memory.max
df -h /workspaces
```

32 CPUを一律に全段階へ割り当てない。生成段階は雀頭牌単位で32 workerまで並列化できる一方、
分類段階はworkerごとにbucketの`HashMap`を保持するため、worker数に応じてピークメモリが増える。
初回構成は次を候補とする。

- 生成worker数: 32
- 分類worker数: 4〜8
- bucket数: 128〜256
- 最低空きdisk: 16 GB。生成recordsの予測値約1.9〜2.7 GBに加え、build成果物と中間生成物の余裕を持つ

生成worker数と分類worker数は別optionとして実装済みである。短時間sampleでbucket最大サイズ、分類時RSS、
cache entries、処理時間を測り、RAMに余裕がある場合だけ分類worker数を増やす。

```bash
lake exe thirteen-tile-report-gen --generation-workers=32 --classification-workers=8 --buckets=256
```

生成完了時だけ`generation.done`をatomic renameで確定する。同じ面子数・bucket数のmarkerと全bucketが
存在すれば、再実行時は生成を省略して分類から始める。markerは形式version、面子数、bucket数、
導出数だけを持つため、追加I/Oは無視できる大きさである。分類途中のcacheやbucket別集計は保存しない。

Codespacesのidle timeoutは既定30分、設定可能な最大値は240分である。terminal入出力はidle timeoutを
リセットするため、分類開始時にbucketごとの進捗を出力する。`tmux`は接続切断への備えにはなるが、
Codespace自体の停止を防ぐものではない。

## 検証項目

分割実装を本番投入する前に、少なくとも次を確認する。

- 10枚形の `tenpaiReports=3,431,439` が一致する。
- 10枚形の reducible `3,416,313`、irreducible `15,126` が一致する。
- 既約コードグループの件数と各 count が一致する。
- shard 順序を変えても最終集計が一致する。
- 同じ入力を再実行して重複カウントが発生しない。
- 強制終了後に `.done` 済み shard を再利用できる。
- キャッシュを有効・無効にして分類結果が一致する。
- cache hit、miss、entries、log サイズ、RSS を記録できる。

## 実装上の優先順位

1. まず外部化された導出レコードと shard 集約を実装する。
2. 生成完了時だけの軽量な`.done` markerによる再開機構を実装する。（完了）
3. 10枚形で外部bucket方式の正しさを検証する。（完了）
4. 13枚形で生成worker数と分類worker数を分離する。（完了）
5. 13枚形の短いサンプルでbucketサイズ、RSS、処理時間を測る。
6. 実測値に基づいてbucket数と分類worker数を調整する。

## 未決定事項

- 13枚形の実際の導出数と tenpai group 数
- 1レコードのエンコードサイズと必要ディスク容量
- shard ごとの cache miss 分布
- 4 GiB環境で許容できる HashMap 上限
- 共有キャッシュがローカルキャッシュより速いかどうか

これらは13枚形の全件計算を開始する前に、短時間のサンプルで測定する。サンプルの結果が
メモリまたはディスク容量の想定を超える場合は、分割数、レコード形式、cache の永続化方式を
見直してから本番計算へ進む。
