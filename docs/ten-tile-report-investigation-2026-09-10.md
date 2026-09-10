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
    有力な容疑者は次の2つだった:
    - `WaitDecompositionCode.canReduceMentsuPreservingWaitCores`
      （グループごとに面子除去候補を再列挙し、待ち核集合を再計算する処理）を
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
    毎回呼ばれていた）。`findWaitCores tiles` をループの外で1回だけ計算するように巻き上げて
    `List.filter` に書き直した（出力は数学的に完全に同一なので、既存の証明（`reducibility_eq_reducible_iff`など）は
    影響を受けない）。
13. 修正後の診断ツールで再測定: `canReduceMentsuPreservingWaitCores` を7枚形の148,809グループ全件に
    適用して `elapsedMs=289130`（**約4分49秒**）。修正前の`332757`（約5分33秒）から約13%の短縮に
    とどまった。改善幅が小さいことから、`mentsuReductions tiles` が返す除去候補の平均件数は
    そもそも少なく（1件前後）、支配的なコストは重複呼び出しではなく、
    `winningPartitions`（`WaitCompletionFinder.findWaitCompletions` 内部の組合せ探索）を
    **グループ1件ごとに少なくとも1回は必ず呼ぶこと自体**が支配的であると判明した。

## 結論

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
  - `n=1 grouped count=5100 groups=1`、`elapsedMs=0`
  - `n=2 grouped count=224502 groups=148809`、`elapsedMs=1`
  - `canReduceMentsuPreservingWaitCores` を148,809件に適用した測定値: `elapsedMs=332757`（約5分32秒）
  - ループ不変量の巻き上げ後の再測定: `elapsedMs=289130`（約4分49秒）
  - `FourTile.tenpaiReports` のbrute-force経路: `elapsedMs=0`

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

- ループ不変量の巻き上げ（実施済み）だけでは約13%しか改善しないため、真の本命は
  「レポート層が既に持っている `report.completions` から `waitCores` を直接求め、
  元の手牌ぶんの `winningPartitions` 探索を丸ごと省略するヘルパー」を追加すること。
  縮小後の手牌については既知データがないため、引き続き `findWaitCores` で探索する。
- 上記ヘルパーを実装したら、同じ診断ツールで7枚形の `canReduceMentsuPreservingWaitCores`
  相当の所要時間を再測定し、どれだけ短縮できたか確認する。
- 10枚形の再実行は、この対策を入れて7枚形で十分な改善を確認してから行う。
