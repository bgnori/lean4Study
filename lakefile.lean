import Lake
open Lake DSL System

package «lean4-project» where
  leanOptions := #[
    -- Enable well-founded recursion default (useful for dependent types)
    ⟨`autoImplicit, false⟩
  ]

require Hammer from git
  "https://github.com/JOSHCLUNE/LeanHammer" @ "v4.28.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

lean_lib «Lean4Project» where
  -- add library configuration options here

lean_lib «Mahjong» where
  -- Mahjong study modules.

lean_lib «MahjongTests» where
  -- Computational regression tests, built explicitly with `lake build MahjongTests`.

lean_lib «MahjongComputations» where
  -- Heavy exhaustive computations, built explicitly with `lake build MahjongComputations`.

lean_exe «four-tile-report-gen» where
  root := `MahjongComputations.FourTileReport

lean_exe «diag-temp» where
  root := `MahjongComputations.DiagTemp

lean_exe «seven-tile-report-gen» where
  root := `MahjongComputations.SevenTileReport

lean_exe «ten-tile-report-gen» where
  root := `MahjongComputations.TenTileReport

lean_exe «ten-tile-shard-report-gen» where
  root := `MahjongComputations.TenTileShardReport

lean_exe «thirteen-tile-report-gen» where
  root := `MahjongComputations.ThirteenTileReport

target fourTileReport pkg : FilePath := do
  let exeJob ← «four-tile-report-gen».fetch
  exeJob.mapM fun exeFile => do
    let reportFile := pkg.dir / "reports" / "four-tile-direct-report.txt"
    proc {
      cmd := exeFile.toString
      args := #[reportFile.toString]
      cwd := some pkg.dir
    }
    return reportFile

target sevenTileReport pkg : FilePath := do
  let exeJob ← «seven-tile-report-gen».fetch
  exeJob.mapM fun exeFile => do
    let reportFile := pkg.dir / "reports" / "seven-tile-report.txt"
    proc {
      cmd := exeFile.toString
      args := #[reportFile.toString]
      cwd := some pkg.dir
    }
    return reportFile

target tenTileReport pkg : FilePath := do
  let exeJob ← «ten-tile-report-gen».fetch
  exeJob.mapM fun exeFile => do
    let reportFile := pkg.dir / "reports" / "ten-tile-report.txt"
    proc {
      cmd := exeFile.toString
      args := #[reportFile.toString]
      cwd := some pkg.dir
    }
    return reportFile

target thirteenTileReport pkg : FilePath := do
  let exeJob ← «thirteen-tile-report-gen».fetch
  exeJob.mapM fun exeFile => do
    let reportFile := pkg.dir / "reports" / "thirteen-tile-direct-report.txt"
    proc {
      cmd := exeFile.toString
      args := #[reportFile.toString]
      cwd := some pkg.dir
    }
    return reportFile

@[default_target]
lean_exe «lean4-project» where
  root := `Main
