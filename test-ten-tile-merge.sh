#!/bin/bash
# Script to merge 10-tile sharded computation results and compare with monolithic run

set -e

NUM_SHARDS=3
SHARD_DIR="/tmp/ten-tile-shards"
MONOLITH_OUTPUT="/tmp/ten-tile-monolith.txt"
MERGED_OUTPUT="$SHARD_DIR/merged.txt"

echo "=== Running monolithic 10-tile report for comparison ===" >&2
{ time -p ./.lake/build/bin/ten-tile-report-gen "$MONOLITH_OUTPUT"; } 2>&1 | tee "$SHARD_DIR/monolith-time.log"

echo ""
echo "=== Extracting key metrics from shards ===" >&2

# Extract and sum tenpaiReports from all shards
echo "Shards tenpaiReports breakdown:"
total_tenpai=0
for ((i=0; i<NUM_SHARDS; i++)); do
    count=$(grep "^tenpaiReports:" "$SHARD_DIR/shard-${i}.txt" | awk '{print $2}')
    echo "  shard $i: $count"
    total_tenpai=$((total_tenpai + count))
done
echo "  TOTAL: $total_tenpai"

echo ""
echo "Monolithic tenpaiReports:"
grep "^tenpaiReports:" "$MONOLITH_OUTPUT"

echo ""
echo "=== Comparing reducibility counts ===" >&2
echo "Shards reducible:"
total_reducible=0
for ((i=0; i<NUM_SHARDS; i++)); do
    count=$(grep -A 1 "### Reducible" "$SHARD_DIR/shard-${i}.txt" | grep "count:" | awk '{print $2}')
    echo "  shard $i: $count"
    total_reducible=$((total_reducible + count))
done
echo "  TOTAL: $total_reducible"

echo ""
echo "Monolithic reducible:"
grep -A 1 "### Reducible" "$MONOLITH_OUTPUT" | grep "count:"

echo ""
echo "Shards irreducible:"
total_irreducible=0
for ((i=0; i<NUM_SHARDS; i++)); do
    count=$(grep -A 1 "### Irreducible" "$SHARD_DIR/shard-${i}.txt" | grep "count:" | awk '{print $2}')
    echo "  shard $i: $count"
    total_irreducible=$((total_irreducible + count))
done
echo "  TOTAL: $total_irreducible"

echo ""
echo "Monolithic irreducible:"
grep -A 1 "### Irreducible" "$MONOLITH_OUTPUT" | grep "count:"

echo ""
echo "=== Cache statistics ===" >&2
echo "Shards waitCoreCache hits/misses:"
total_hits=0
total_misses=0
for ((i=0; i<NUM_SHARDS; i++)); do
    hits=$(grep "^waitCoreCacheHits:" "$SHARD_DIR/shard-${i}.txt" | awk '{print $2}')
    misses=$(grep "^waitCoreCacheMisses:" "$SHARD_DIR/shard-${i}.txt" | awk '{print $2}')
    echo "  shard $i: hits=$hits, misses=$misses"
    total_hits=$((total_hits + hits))
    total_misses=$((total_misses + misses))
done
echo "  TOTAL: hits=$total_hits, misses=$total_misses"

echo ""
echo "Monolithic cache:"
grep -E "^waitCoreCacheHits:|^waitCoreCacheMisses:|^waitCoreCacheEntries:" "$MONOLITH_OUTPUT"
