import Lake
open Lake DSL

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

@[default_target]
lean_exe «lean4-project» where
  root := `Main
