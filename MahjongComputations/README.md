# MahjongComputations

This directory is for expensive or exhaustive Mahjong computations that should
not be part of normal `Mahjong` builds.

Build it explicitly when needed:

```bash
lake build MahjongComputations
```

Generate the four-tile text report:

```bash
lake build fourTileReport
```

The report is written to `reports/four-tile-report.txt`.

Generate the seven-tile text report:

```bash
lake build sevenTileReport
```

The report is written to `reports/seven-tile-report.txt`.

Current modules:

- `FourTile.lean`: enumerates all legal four-tile multisets and computes tenpai
  waits, wait classifications, reducibility, and abstract wait-reading codes.
- `FourTileReport.lean`: writes the exhaustive four-tile report as a text file.
- `SevenTile.lean`: folds all legal seven-tile multisets into aggregate wait
  report data without retaining every shape.
- `SevenTileReport.lean`: writes the exhaustive seven-tile aggregate report as a
  text file.