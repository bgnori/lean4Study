# Mahjong Modules

This directory contains the Mahjong wait-classification formalization used as the main Lean study exercise in this repository.

## Reading Order

1. `Basic.lean`
   - Mahjong tiles: suits, ranks, honors, physical tiles, deck cardinality.
   - Tile formatting helpers.

2. `Pattern.lean`
   - Shared tile-pattern machinery.
   - Taatsu, toitsu, tanki, shuntsu, and mentsu candidates.

3. `FourTileWait.lean`
   - Four-tile extraction syntax and named classification vocabulary.
   - Ambiguity and reducibility properties of each classification name.

4. `FourTileWait/Specification.lean`
   - Analyzer-independent profiles and the reference classification specification.

5. `FourTileWait/Analysis.lean`
   - Observation of profiles from standard-form winning decompositions.
   - The executable classifier and its soundness/completeness theorems.
   - Checked examples for all ten named classifications.

6. `Hand.lean`
   - Hand sizes used in the study project.
   - Enumeration of possible hand extractions from physical tiles.

7. `Shape.lean`
   - The `Shape` data type: one wait tile and one completed decomposition.
   - Completed chunk types and canonical ordering.

8. `ShapeFinder.lean`
   - Shared semantics: `IsStandardAgari`, `IsWaitFor`, `IsTenpai`, and `Wait`.
   - `ShapeFinder.find`, executable decomposition discovery, and irreducibility.

9. `ShapeCode.lean`
   - Codes already-found `List Shape` values without performing discovery.
   - `find...` convenience functions explicitly compose `ShapeFinder` with coding.
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
import Mahjong.FourTileWait
import Mahjong.ShapeFinder
import Mahjong.ShapeCode
```

The old `mj.lean` file is kept only as a compatibility import for older notes.

## Validation

```bash
lake build Mahjong
```

For a single file:

```bash
lake env lean Mahjong/ShapeFinder.lean
```

## Documentation Style

The Lean files intentionally contain checked examples near the definitions they explain.  When adding a new classification rule or normalization scheme, prefer adding a small `example` close to the relevant definition so the documentation remains executable.
