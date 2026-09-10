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
    有力な容疑者は次の2つ（この文書の時点では特定作業を継続中）:
    - `WaitDecompositionCode.canReduceMentsuPreservingWaitCores`
      （グループごとに面子除去候補を再列挙し、待ち核集合を再計算する処理）を
      牌姿グループ全件（7枚形で148,809件）に対して呼ぶコスト。
    - `FourTile.tenpaiReports`（`allFourTileShapes` から全4枚形66,045件を総当たりで
      `WaitCompletionFinder`/`determineReducibility`/`findWaitDecompositionCodes` に通す、
      direct derivationとは別の brute-force 経路）が4枚形レポートに残っている影響。

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

- `canReduceMentsuPreservingWaitCores` および `FourTile` の brute-force経路（`tenpaiReports`）が
  実際のボトルネックかどうかを、計測を修正した診断ツールで確定する。
- ボトルネックが確認できたら、そこを軽量化するか、10枚形・13枚形のレポートでは
  その経路を回避する設計に変更するかを検討する。
- 10枚形の再実行は、上記の切り分けが終わってから行う。
