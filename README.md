# lean4Study

Lean 4 and mathlib study repository. The main worked example is a formalization of Mahjong wait classification: tiles, tile patterns, standard-form wait semantics, named wait classifications, and executable four-tile examples that Lean checks during builds.

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
│   ├── Wait.lean
│   ├── Wait/Specification.lean
│   ├── Wait/Analysis.lean
│   ├── Hand.lean
│   ├── WaitCompletion.lean
│   ├── WaitCompletionFinder.lean
│   ├── WaitDecompositionCode.lean
│   ├── DirectWaitGeneration.lean
│   ├── Tenpai.lean
│   └── README.md
├── MahjongTests/          # Explicitly-built computational regression tests
├── MahjongComputations/   # Explicitly-built exhaustive computations and reports
├── docs/                  # Reading order and Lean/domain vocabulary
└── reports/               # Generated computation reports
```

## Build

```bash
lake build
```

To check only the Mahjong modules:

```bash
lake build Mahjong
```

To run the computational regression tests:

```bash
lake build MahjongTests
```

To run expensive/exhaustive Mahjong computations:

```bash
lake build MahjongComputations
```

To generate the four-tile and seven-tile computation reports:

```bash
lake build fourTileReport
lake build sevenTileReport
```

The reports are written to `reports/four-tile-direct-report.txt` and
`reports/seven-tile-report.txt`.

To check a single file directly:

```bash
lake env lean Mahjong/WaitCompletionFinder.lean
```

## Documentation

Reader-facing guides:

- [docs/introduction.md](docs/introduction.md): Japanese introduction to Lean4 and proof-carrying programs for this project.
- [docs/reading-order.md](docs/reading-order.md): linear reading path for readers new to Lean.
- [docs/lean-vocabulary.md](docs/lean-vocabulary.md): recurring Lean syntax and proof vocabulary.
- [docs/domain-vocabulary.md](docs/domain-vocabulary.md): project-specific Mahjong terminology.

Writer and maintenance notes:

- [docs/documentation-policy.md](docs/documentation-policy.md): division between reader-facing guides, vocabulary pages, and maintenance notes.
- [docs/proof-comment-policy.md](docs/proof-comment-policy.md): division of responsibility between source comments and guides.
- [docs/review-backlog.md](docs/review-backlog.md): design and naming questions discovered during documentation.
- [Mahjong/README.md](Mahjong/README.md): module-level overview.
