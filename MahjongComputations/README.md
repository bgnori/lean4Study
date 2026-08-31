# MahjongComputations

This directory is for expensive or exhaustive Mahjong computations that should
not be part of normal `Mahjong` builds.

Build it explicitly when needed:

```bash
lake build MahjongComputations
```

Current modules:

- `FourTile.lean`: enumerates all legal four-tile multisets and computes tenpai
  waits, wait classifications, reducibility, and abstract decomposition codes.