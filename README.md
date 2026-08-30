# lean4Study

Lean 4 and mathlib study repository. The main worked example is a formalization of Mahjong wait classification: tiles, tile patterns, standard-form wait semantics, named four-tile classifications, and executable examples that Lean checks during builds.

[日本語版はこちら](README.ja.md)

## Goals

- Learn Lean 4 by modeling concrete domains with types.
- Keep examples executable with `example ... := by native_decide` where possible.
- Grow proofs alongside computation instead of treating documentation, tests, and implementation as separate artifacts.

## Project Layout

```text
.
├── Main.lean              # Small Lean/mathlib practice examples
├── Haskell.lean           # Basic list/function practice notes
├── NaturalLimited.lean    # Finite-type/cardinality study notes
├── Lean4Project.lean      # Library entry point
├── Mahjong.lean           # Mahjong module entry point
├── Mahjong/               # Mahjong wait-classification study modules
│   ├── Basic.lean
│   ├── Pattern.lean
│   ├── FourTileWait.lean
│   ├── FourTileWait/Specification.lean
│   ├── FourTileWait/Analysis.lean
│   ├── Hand.lean
│   ├── Shape.lean
│   ├── ShapeFinder.lean
│   ├── ShapeCode.lean
│   ├── Tenpai.lean
│   └── README.md
└── mj.lean                # Compatibility import for older notes
```

## Build

```bash
lake build
```

To check only the Mahjong modules:

```bash
lake build Mahjong
```

To check a single file directly:

```bash
lake env lean Mahjong/ShapeFinder.lean
```

## Documentation Style

Lean source files are the primary documentation.  Module comments explain the intent, while checked `example` blocks serve as executable specifications.  README files give navigation and project context rather than duplicating every definition.
