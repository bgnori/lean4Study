import Lake
open Lake DSL System

package «lean4-project» where
  leanOptions := #[
    -- Enable well-founded recursion default (useful for dependent types)
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

lean_lib «Lean4Project» where
  -- add library configuration options here

lean_lib «Mahjong» where
  -- Mahjong wait-classification study modules.

lean_lib «MahjongTests» where
  -- Computational regression tests, built explicitly with `lake build MahjongTests`.

lean_lib «MahjongComputations» where
  -- Heavy exhaustive computations, built explicitly with `lake build MahjongComputations`.

lean_exe «four-tile-report-gen» where
  root := `MahjongComputations.FourTileReport

lean_exe «seven-tile-report-gen» where
  root := `MahjongComputations.SevenTileReport

target fourTileReport pkg : FilePath := do
  let exeJob ← «four-tile-report-gen».fetch
  exeJob.mapM fun exeFile => do
    let reportFile := pkg.dir / "reports" / "four-tile-report.txt"
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

@[default_target]
lean_exe «lean4-project» where
  root := `Main
