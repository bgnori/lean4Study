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
   - A broad `HasNobetanReading` alias separated from narrow whole-profile classification.

5. `Wait/Analysis.lean`
   - Observation of profiles from standard-form winning decompositions.
   - The executable classifier and its soundness/completeness theorems.
   - Evidence-indexed reducibility computation for concrete tenpai hands.

6. `Hand.lean`
   - Hand sizes used in the study project.
   - Verified enumeration of exact physical-tile extractions.

7. `Decomposition.lean`
   - The `Decomposition` data type: one wait tile and one completed decomposition.
   - Completed chunk types and canonical ordering.

8. `DecompositionFinder.lean`
   - Shared semantics: `IsStandardAgari`, `IsWaitFor`, `IsTenpai`, and `Wait`.
   - Legal tenpai sizes and physical copy-count validation.
   - `DecompositionFinder.find`, executable decomposition discovery, and evidence-indexed irreducibility.

9. `DecompositionCode.lean`
   - Codes already-found `List Decomposition` values without performing discovery.
   - `find...` convenience functions explicitly compose `DecompositionFinder` with coding.
   - The 53 one-suit irreducible seven-tile examples.

10. `Tenpai.lean`
   - A thin bridge from physical `Hand` values to the single semantic `Wait` type.

## Import Entry Points

Use the top-level module when you want the whole Mahjong development:

```lean
import Mahjong
```

For focused work, import the smallest module that contains the definitions you need:

```lean
import Mahjong.Wait
import Mahjong.DecompositionFinder
import Mahjong.DecompositionCode
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

For a single file:

```bash
lake env lean Mahjong/DecompositionFinder.lean
```

## Documentation Style

Keep small proof examples near the definitions they explain. Put expensive
`native_decide` regression tests under `MahjongTests/` so they are checked by
the explicit test target without slowing normal library builds.
