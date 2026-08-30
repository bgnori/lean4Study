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
   - Four-tile wait extractions and wait kinds.
   - Ambiguity and reducibility classification.
   - Concrete checked examples for each four-tile wait kind.

4. `SevenTileWait.lean`
   - Seven-tile waits as a complete mentsu plus a four-tile wait.
   - Checked examples and extraction-count theorems.

5. `Hand.lean`
   - Hand sizes used in the study project.
   - Enumeration of possible hand extractions from physical tiles.

6. `StandardWait.lean`
   - Normal-form wait analysis over lists of tile types.
   - Winning decompositions, irreducibility, normalized decompositions, and abstract shape codes.
   - Larger executable examples, including the 53 one-suit irreducible seven-tile examples.

7. `Tenpai.lean`
   - Dependent `Tenpai` relation tying hand sizes to wait witnesses.
   - Currently a small bridge layer for one-, four-, and seven-tile tenpai evidence.

## Import Entry Points

Use the top-level module when you want the whole Mahjong development:

```lean
import Mahjong
```

For focused work, import the smallest module that contains the definitions you need:

```lean
import Mahjong.FourTileWait
import Mahjong.StandardWait
```

The old `mj.lean` file is kept only as a compatibility import for older notes.

## Validation

```bash
lake build Mahjong
```

For a single file:

```bash
lake env lean Mahjong/StandardWait.lean
```

## Documentation Style

The Lean files intentionally contain checked examples near the definitions they explain.  When adding a new classification rule or normalization scheme, prefer adding a small `example` close to the relevant definition so the documentation remains executable.
