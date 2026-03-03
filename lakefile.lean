import Lake
open Lake DSL

package «lean4-project» where
  leanOptions := #[
    -- Enable well-founded recursion default (useful for dependent types)
    ⟨`autoImplicit, false⟩
  ]

lean_lib «Lean4Project» where
  -- add library configuration options here

@[default_target]
lean_exe «lean4-project» where
  root := `Main
