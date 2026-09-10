import MahjongComputations.Common
import MahjongComputations.FourTile
import MahjongComputations.SevenTile

open MahjongComputations

def main : IO Unit := do
  let t0 ← IO.monoMsNow
  let count1 := foldCanonicalDirectWaitDerivations (n := 1) 0 (fun acc _ => acc + 1)
  IO.println s!"n=1 fold-only count={count1}"
  let t1 ← IO.monoMsNow
  IO.println s!"elapsedMs={t1 - t0}"

  let t2 ← IO.monoMsNow
  let generated1 := canonicalWaitCompletionGroups 1
  IO.println s!"n=1 grouped count={generated1.enumeratedDerivations} groups={generated1.groups.length}"
  let t3 ← IO.monoMsNow
  IO.println s!"elapsedMs={t3 - t2}"

  let t4 ← IO.monoMsNow
  let count2 := foldCanonicalDirectWaitDerivations (n := 2) 0 (fun acc _ => acc + 1)
  IO.println s!"n=2 fold-only count={count2}"
  let t5 ← IO.monoMsNow
  IO.println s!"elapsedMs={t5 - t4}"

  let t6 ← IO.monoMsNow
  let generated2 := canonicalWaitCompletionGroups 2
  IO.println s!"n=2 grouped count={generated2.enumeratedDerivations} groups={generated2.groups.length}"
  let t7 ← IO.monoMsNow
  IO.println s!"elapsedMs={t7 - t6}"

  let t8 ← IO.monoMsNow
  let reducibleCount := (generated2.groups.filter fun g =>
    WaitDecompositionCode.canReduceMentsuPreservingWaitCores g.tiles).length
  IO.println s!"n=2 canReduceMentsuPreservingWaitCores reducibleCount={reducibleCount}"
  let t9 ← IO.monoMsNow
  IO.println s!"elapsedMs={t9 - t8}"

  let t10 ← IO.monoMsNow
  let fourBruteForceCount := FourTile.tenpaiReports.length
  IO.println s!"four-tile brute-force tenpaiReports={fourBruteForceCount}"
  let t11 ← IO.monoMsNow
  IO.println s!"elapsedMs={t11 - t10}"

