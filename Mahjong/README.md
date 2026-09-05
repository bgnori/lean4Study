# Mahjong Modules

This directory contains the Mahjong wait-classification formalization used as the main Lean study exercise in this repository.

## Reading Order

1. `Basic.lean`
   - Mahjong tiles: suits, ranks, honors, physical tiles, deck cardinality.
   - Tile formatting helpers.

2. `Pattern.lean`
   - Shared tile-pattern machinery.
   - Taatsu, toitsu, tanki, shuntsu, and mentsu candidates.

3. `Wait.lean`
   - Size-independent wait extraction syntax and named classification vocabulary.
   - Ambiguity metadata that is determined by each classification name.

4. `Wait/Specification.lean`
   - Analyzer-independent, rule-based classification evidence.
   - A broad `ContainsNobetan` condition separated from narrow whole-profile classification.

5. `Wait/Analysis.lean`
   - Observation of profiles from standard-form wait completions.
   - The executable classifier and its soundness/completeness theorems.
   - Evidence-indexed reducibility computation for concrete tenpai hands.

6. `Hand.lean`
   - Hand sizes used in the study project.
   - Verified enumeration of exact physical-tile extractions.

7. `WaitCompletion.lean`
   - The `WaitCompletion` data type: one wait tile and one winning partition.
   - Winning components and their canonical ordering.

8. `WaitCompletionFinder.lean`
   - Shared semantics: `IsStandardAgari`, `IsWaitFor`, `IsTenpai`, and `Wait`.
   - Legal tenpai sizes and physical copy-count validation.
   - `WaitCompletionFinder.findWaitCompletions`, executable completion discovery, and evidence-indexed irreducibility.

9. `WaitDecompositionCode.lean`
   - Decomposes and codes already-found `List WaitCompletion` values without performing discovery.
   - `find...` convenience functions explicitly compose `WaitCompletionFinder` with coding.
   - The 53 one-suit irreducible seven-tile examples.

10. `DirectWaitGeneration.lean`
   - Generates normalized wait derivations directly from completed winning shapes.
   - Proves exact correspondence with `WaitCompletionFinder` in the standard-hand range.
   - Provides a noncomputable perfect-hash specification between all derivations and finite indices.

11. `Tenpai.lean`
   - A thin bridge from physical `Hand` values to the single semantic `Wait` type.

## Import Entry Points

Use the top-level module when you want the whole Mahjong development:

```lean
import Mahjong
```

For focused work, import the smallest module that contains the definitions you need:

```lean
import Mahjong.Wait
import Mahjong.WaitCompletionFinder
import Mahjong.WaitDecompositionCode
```

## Validation

```bash
lake build Mahjong
```

The computational regression tests are kept out of the production library so
that normal builds do not repeatedly compile `native_decide` proofs:

```bash
lake build MahjongTests
```

Expensive exhaustive computations are also separated from the production
library:

```bash
lake build MahjongComputations
```

To write the four-tile exhaustive report:

```bash
lake build fourTileReport
```

For a single file:

```bash
lake env lean Mahjong/WaitCompletionFinder.lean
```

## Development Notes

Keep small proof examples near the definitions they explain. Put expensive
`native_decide` regression tests under `MahjongTests/` so they are checked by
the explicit test target without slowing normal library builds. Put broader
enumerations and exploratory computations under `MahjongComputations/`.

For the full documentation policy, see [docs/documentation-policy.md](../docs/documentation-policy.md).
