# lean4Study

Lean 4 and mathlib study repository. The main worked example formalizes Mahjong tiles, tile patterns, standard-form wait semantics, wait cores, and executable computations that Lean checks during builds.

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
├── Mahjong/               # Mahjong study modules
│   ├── Basic.lean
│   ├── Pattern.lean
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

### Codespaces for large computations

The dev container declares minimum host requirements of 16 CPUs, 64 GB RAM, and 64 GB storage.
It deliberately applies no Docker CPU or memory limits, allowing the container to use the selected
Codespaces machine. After creating or rebuilding the container, verify it with:

```bash
nproc
cat /sys/fs/cgroup/memory.max
df -h /workspaces
```

Run long computations inside `tmux` and set the Codespaces idle timeout to 240 minutes. Terminal
output resets the idle timeout, so computations that may otherwise be silent for hours should emit
periodic progress. Do not automatically use all CPUs for bucket classification: each classification
worker retains a bucket-sized hash map. A suitable initial command is:

```bash
lake exe thirteen-tile-report-gen --generation-workers=16 --classification-workers=8 --buckets=256
```

If organization policy offers a 32-core machine, generation workers can be raised to 32.

After generation completes, `.lake/build/thirteen-tile-buckets/generation.done` records the phase
boundary. Re-running with the same settings reuses those buckets if classification was interrupted.
The wait-core cache and individual bucket results are not checkpointed. Remove the bucket directory
to force regeneration.

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
