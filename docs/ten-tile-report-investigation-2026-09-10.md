# 10枚形レポート実行に向けた試行錯誤記録 2026-09-10

この文書は、`lake build tenTileReport` を実際に完走させるための調査・実装の経過を時系列で残す。
読者向けの説明ではなく、今後同じ調査をやり直さずに済むための作業ログである。

## 経緯の要約

1. `MahjongComputations.TenTile`/`ThirteenTile`（と対応するReport、lakefileターゲット）を、既存の
   `FourTile`/`SevenTile` と同じ構造で新規追加した。
2. `lake build tenTileReport` を実行 → **exit code 137（`SIGKILL`、OOM Kill）**。
3. 原因調査 → コンテナのcgroupメモリ上限が4GiBであること、および
   `DirectWaitGeneration.directWaitDerivations n` が面子割り当てを `Fin n → MentsuCandidate` という
   **順序付き関数として `55^n` 通り全列挙**してから `Seed.valid` の正規化条件
   （`mentsuCanonical`）で並べ替え違いの重複を捨てる実装であることを特定した。
4. 面子の割り当てを最初から非減少列（重複組合せ）だけで直接列挙する
   `MahjongComputations.canonicalDirectWaitDerivations`（のちに `canonicalWaitCompletionGroups` へ発展）を実装。
   `mentsuCanonical` と同じ順序基準を使うため、最終結果は `directWaitDerivations` と一致する
   （7枚形で `enumeratedDerivations`・グループ数・グループ内容が完全一致することを確認済み）。
5. それでも `lake build tenTileReport` は9分42秒粘った末に再度 exit 137。
   → 原因は「全件を `List` として一括生成してから牌姿キーでソートしてグループ化する」という
   構造そのものにあると判断し、`Std.HashMap` を使ったストリーミング集約
   （生成した瞬間にハッシュマップへ反映し、`List` として保持しない）へ書き換えた。
6. ストリーミング版も7枚形で旧実装と完全一致することを確認（生成件数・グループ数・
   ソート済みグループ配列が一致）。
7. ユーザーが10枚形の実行を2時間経過後に打ち切り。実行時間が期待より大幅に長かった。
8. 検証のため `FourTile`/`SevenTile` も同じ「正準生成＋ストリーミング」へ切り替えて実測:
   - `fourTileReport`: 38.85秒
   - `sevenTileReport`: 4分59秒（旧実装の5分27秒とほぼ変わらず）
9. 生成・グループ化そのものが遅いのか切り分けるため、診断用の一時実行ファイルで
   `foldCanonicalDirectWaitDerivations`・`canonicalWaitCompletionGroups` の所要時間を計測。
   **ただし初回計測は `let`束縛の直後にタイマーを止めてしまい、実際の強制評価（文字列化）が
   計測区間の外で起きていたため、常に `elapsedMs=0` という誤った結果になった。**
   `IO.println` を計測区間の内側に移してから再計測すると、7枚形の生成・グループ化
   （生の候補224,502件、グループ148,809件）は **1ms未満** で終わることを確認した。
10. これにより、生成・グループ化のアルゴリズムはすでに高速であり、`fourTileReport`/`sevenTileReport`
    全体の実行時間（38秒・5分）を支配しているのは**別の処理**であると判明した。
      牌姿グループ全件（7枚形で148,809件）に対して呼ぶコスト。
    - `FourTile.tenpaiReports`（`allFourTileShapes` から全4枚形66,045件を総当たりで
      `WaitCompletionFinder`/`determineReducibility`/`findWaitDecompositionCodes` に通す、
      direct derivationとは別の brute-force 経路）が4枚形レポートに残っている影響。
11. 修正済みの診断ツールで実測した結果、犯人が確定した。
    - `canReduceMentsuPreservingWaitCores` を7枚形の148,809グループ全件に適用:
      `elapsedMs=332757`（**約5分32秒**）。これは `sevenTileReport` 全体の実測（約5分）と
      ほぼ一致し、実行時間のほぼ全量がこの1関数に集中していることを裏付けた。
    - `FourTile.tenpaiReports`（brute-force経路、66,045件総当たり）: `elapsedMs=0`。
      こちらはボトルネックではないと判明した。4枚形の38秒も、グループ数が
      3,756件と少ないだけで、同じ`canReduceMentsuPreservingWaitCores`が支配していると見てよい。
12. 可約性判定側の高速化の第1歩として、`WaitDecompositionCode.waitCorePreservingMentsuReductions`を
    修正した。元の実装は `do` 記法で `findWaitCores tiles`（除去前の元の手牌の待ち核）を
    `mentsuReductions tiles` が返す候補の数だけ毎回再計算していた（`tiles`にしか依存しないのに候補ループの中で
    `List.filter` に書き直した（出力は数学的に完全に同一なので、既存の証明（`reducibility_eq_reducible_iff`など）は
    影響を受けない）。
13. 修正後の診断ツールで再測定: `canReduceMentsuPreservingWaitCores` を7枚形の148,809グループ全件に
    とどまった。改善幅が小さいことから、`mentsuReductions tiles` が返す除去候補の平均件数は
    そもそも少なく（1件前後）、支配的なコストは重複呼び出しではなく、
    `winningPartitions`（`WaitCompletionFinder.findWaitCompletions` 内部の組合せ探索）を


生成・グループ化（正準生成＋ストリーミング化）の最適化は正しく機能しており、メモリ超過の
原因は解消できた。しかし `fourTileReport`/`sevenTileReport`/`tenTileReport` の**実行時間**を
支配しているのは生成側ではなく、`WaitDecompositionCode.canReduceMentsuPreservingWaitCores`
（可約性判定）である。この関数は牌姿グループ1件ごとに `mentsuReductions` で面子除去候補を
列挙し、`findWaitCores` を複数回呼び直して待ち核集合を比較しており、グループ数に比例して
重くなる。10枚形はグループ数が7枚形よりさらに大きくなる見込みのため、生成側の最適化だけでは
実行時間の問題を解決できず、次に着手すべきは可約性判定側の高速化である。

ループ不変量の巻き上げ（第1歩）だけでは改善は約13%に留まった。本当のボトルネックは
「元の手牌の待ち核を求めるために、すでに`report.completions`として知っている情報を使わず、
`WaitCompletionFinder.findWaitCompletions`でゼロから探索し直していること」にあると見ている。次の手は、
レポート層専用の関数で `waitCores report.completions`（既知の完成情報から直接待ち核を求める）を
使い、元の手牌分の探索を丸ごと省略することである（縮小後の手牌は既知データがないため引き続き探索が必要）。
検証済みの `canReduceMentsuPreservingWaitCores` 自体の定義は変えず、レポート層専用の新しいヘルパーとして
追加する方針で進める。

## 実行結果（最新の確認値）

以下は、このセッションで実際に確認できた代表的な実行結果である。

- `lake build fourTileReport` → `exit code 0`、実行時間は約38.85秒
- `lake build sevenTileReport` → `exit code 0`、実行時間は約4分59秒
- `lake build diag-temp && ./.lake/build/bin/diag-temp` → `exit code 0`
  - `n=1 fold-only count=5100`、`elapsedMs=0`
  - `n=1 grouped count=5100 groups=3756`、`elapsedMs=0`
  - `n=2 grouped count=224502 groups=148809`、`elapsedMs=1`
  - `canReduceMentsuPreservingWaitCores` を148,809件に適用した測定値: `elapsedMs=332757`（約5分32秒）
  - ループ不変量の巻き上げ後の再測定: `elapsedMs=289130`（約4分49秒）
これらの値から、生成・グループ化自体はすでに高速であり、レポート全体の時間は
`WaitDecompositionCode.canReduceMentsuPreservingWaitCores` の判定コストが支配している。
最適化前後の差は約13%であり、再計算が減ったものの真のボトルネックは
「元の手牌の待ち核を再探索している」ことにある。

## 教訓・注意点

- **`lake env lean --run foo.lean` はインタプリタ実行であり、`lake build` でコンパイルして
  できたバイナリを直接実行するより10〜50倍以上遅い。** 検証・ベンチマーク用のスクリプトは
  一時的に `lakefile.lean` へ `lean_exe` を追加してコンパイル実行し、確認後に
  一時モジュールと `lean_exe` 定義を削除する。
- **Lean4の `let x := 式` は式を即座に強制評価しない。** `IO.monoMsNow` で区間計測する際、
  区間の終端を測った直後に `IO.println` などで値を消費すると、実際の計算はその消費側で
  行われるため計測区間の外に漏れる。計測したい処理は、必ず「強制的に消費する操作
  （出力・比較・パターンマッチなど）」を計測区間の内側に含めること。
- コンテナのcgroupメモリ上限は `cat /sys/fs/cgroup/memory.max` で確認できる（このセッションでは
  4GiB）。`exit code 137` は SIGKILL（128+9）であり、OOM Killの強い手がかりになる。
- `Seed.valid` の `mentsuCanonical`/`selectedIsCanonical` は、もともと「面子の並べ替えや
  同一面子の重複選択による水増しを除く」ための正規化条件として実装されていた。
  つまり `directWaitDerivations` は元から「非正準な生成物を捨てる」設計を意図しており、
  生成側を非減少列だけに絞る最適化（`canonicalDirectWaitDerivations`）は、既存の意図から
  外れた変更ではなく、無駄な生成をなくしただけの最適化だと言える。

## 未解決・次の一手

### 10枚形レポートの完走結果（2026-09-11）

`time lake build tenTileReport` が終了コード`0`で完走した。実時間は`17分23.521秒`、
ユーザー時間は`17分7.760秒`、システム時間は`4.416秒`だった。

生成されたレポートの主要値は次の通り。

- `allTenTileShapes: 1900269316`
- `enumeratedDerivations: 5536779`
- `tenpaiReports: 3431439`
- reducible: `3416313`
- irreducible: `15126`
- wait-core cache: `3701891 hits / 295762 misses / 295762 entries`
- irreducible code groups: `199`

レポート内の`calculationElapsedMs: 0`は、7枚形と同様に遅延評価のため測定値として採用しない。
上記の`time`による実時間を正式な実測値とする。13枚形レポートはこの時点では実行していない。

### 13枚形レポートの実行時間見積もり（2026-09-11時点）

13枚形は `canonicalWaitCompletionGroups 4`、10枚形は
`canonicalWaitCompletionGroups 3` を使う。正準面子組合せ数だけを比較すると、増加率は

$$
\frac{\binom{58}{4}}{\binom{57}{3}} \approx 14.5
$$

である。さらに、完成形から待ち部品を選ぶ候補数も4面子から5部品へ増えるため、
13枚形の導出数は10枚形の単純な14.5倍より大きくなり、概算で約18〜25倍、
すなわち約1億〜1.4億件になると見積もった。

10枚形の実測（`3,431,439` tenpai reports、`17分23.521秒`）から、13枚形の
tenpai group 数は約5,000万〜8,500万件と推定した。同じ1件あたりの処理時間だけを
仮定すれば4〜7時間程度だが、13枚形では面子除去後が10枚形になるため、待ち探索自体も
10枚形より重くなる可能性がある。これを加味した実行時間の見積もりは次の通りである。

- 楽観的: 4〜6時間
- 中心値: 8〜12時間
- 悲観的: 12〜24時間以上

最大の不確定要素は、13枚形の実際のtenpai group数、cache miss数、およびキャッシュの
メモリ使用量である。10枚形では`295,762` entriesだったキャッシュが13枚形では数百万件に
増える可能性があり、4GiBのcgroupメモリ制限下ではOOMになるリスクも残る。
したがって、この見積もりだけを根拠に13枚形の全件生成を開始しない。実行する場合は、まず
短時間のサンプリングで導出数、group数、cache miss数、メモリ使用量を測定し、再見積もりする。

既約性判定は、意味論を変えない小さい変更から次の順で改善する。

1. **存在判定を `filter` と `isEmpty` の組み合わせから `List.any` へ変更する。**
  成功候補を1件見つけた時点で評価を止める。削減候補一覧を返す
  `waitCorePreservingMentsuReductions` は既存APIとして残し、Boolを返す判定だけを直接実装する。
2. **縮小手牌に対する待ち探索の二重実行を除く。**
  現在は `waitingTiles remaining` の後に `findWaitCores remaining` が内部でも待ちを探索する。
  `findWaitCores remaining` の非空性で聴牌性を代用できることを、定理または全件比較で確認してから統合する。
3. **縮小手牌の待ち核を牌多重集合キーでキャッシュする。**
  異なる元牌姿から同じ縮小牌姿へ到達する場合の再探索を避ける。結果一致だけでなく、
  キャッシュの件数・ピークメモリ・経過時間を測り、4GiB制限下で逆効果にならないことを確認する。

各段階で7枚形148,809グループを全件評価し、既存実装の基準値
`reducibleCount=144516` と一致することを確認する。意味論の一致を確認した後に所要時間を比較し、
改善が認められた変更だけを残す。10枚形の再実行は、この段階的検証が完了してから行う。

### 段階1の実施結果: `List.any` 化は不採用

`waitCorePreservingMentsuReductions` は互換性のため残し、`canReduceMentsuPreservingWaitCores` と
レポート用ヘルパーの存在判定だけを `List.any` で短絡化して全件測定した。結果はいずれも
`reducibleCount=144516` であり、意味論は既存実装と一致した。一方、所要時間は次の通りだった。

- 汎用判定: `296032ms` → `304093ms`（約2.7%増）
- completion再利用版: `133254ms` → `137980ms`（約3.5%増）

測定揺らぎの範囲も考えられるが、少なくとも改善は確認できなかった。成功候補が十分早い位置に
偏っていないこと、またはLeanの評価・最適化により元の `filter` 非空判定との差が小さいことが考えられる。
「改善が認められた変更だけを残す」という方針に従い、`List.any` 化はコードから戻した。
次は段階2の二重探索除去について、まず非空性の同値条件を確認する。

### 段階2の実施結果: 単純な二重探索除去は不採用

`WaitCompletionFinder.findWaitCompletions_ne_nil_iff` を追加し、任意の牌姿について
`findWaitCompletions tiles ≠ [] ↔ waitingTiles tiles ≠ []` を証明した。この定理を根拠として、
各縮小手牌では `findWaitCompletions remaining` を1回だけ実行し、その結果の非空性と
`waitCores remainingCompletions` を同時に利用する形を測定した。汎用判定は
`reducibleCount=144516` を維持したが `308083ms` で、変更前の `296032ms` より遅かった。
completion再利用版も3分を超え、変更前の `133254ms` を明確に上回った時点で測定を停止した。

`findWaitCompletions` 自体が内部で `waitingTiles` と完成分割列挙を行うため、外側の呼び出しを単純に
まとめても支配的な探索を減らせなかったと考えられる。実行経路の変更は戻したが、非空性同値定理は
APIの意味を明示する有用な結果として残した。次は段階3として、縮小牌姿ごとの探索結果を
`tileMultisetKey` で共有するキャッシュを検討する。

### 段階3の実施結果: 4枚形・7枚形へキャッシュを導入

縮小牌姿の待ち核集合を `tileMultisetKey` で report-wide に共有する
`WaitCoreCache` を導入した。4枚形と7枚形をコンパイル済みジェネレータで実行し、
シェル組み込み `time -p` の `real` を測定した。10枚形・13枚形は実行していない。

- 4枚形: `36.68s`、`3756` tenpai reports、`1647` reducible、`2109` irreducible
  - `1802` hits / `34` misses / `34` entries
- 7枚形: `12.66s`、`148809` tenpai reports、`144516` reducible、`4293` irreducible
  - `155229` hits / `6363` misses / `6363` entries

比較対象の既存測定は、4枚形が約`38.85s`、7枚形が約`4分59秒`だった。
今回の測定では、4枚形は約`5.6%`短縮、7枚形は約`95.8%`短縮となる。
ただし、7枚形の比較対象はキャッシュ導入前の別経路を含む測定であり、キャッシュ単独の効果とは
断定しない。件数が一致していることと、キャッシュによる再利用量を確認した結果として記録する。
