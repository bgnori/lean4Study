#!/bin/bash
# Test script for 10-tile sharded computation with 3 shards
# Measures execution time and memory usage for each shard

set -euo pipefail

NUM_SHARDS=3
OUTPUT_DIR="/tmp/ten-tile-shards"
mkdir -p "$OUTPUT_DIR"

if [[ ! -x ./.lake/build/bin/ten-tile-shard-report-gen ]]; then
    echo "error: shard executable is missing; run 'lake build ten-tile-shard-report-gen' first" >&2
    exit 1
fi

# Function to run a single shard and measure time + memory
run_shard() {
    local shard_idx=$1
    local output_file="$OUTPUT_DIR/shard-${shard_idx}.txt"
    
    echo "=== Running shard ${shard_idx}/${NUM_SHARDS} ===" >&2
    
    # Use /usr/bin/time if available (provides max RSS), fall back to shell time
    if command -v /usr/bin/time &> /dev/null; then
        /usr/bin/time -v \
            ./.lake/build/bin/ten-tile-shard-report-gen \
            --shard="$shard_idx" --num-shards="$NUM_SHARDS" \
            "$output_file" 2>&1 | tee "$OUTPUT_DIR/shard-${shard_idx}-time.log"
    else
        local time_log="$OUTPUT_DIR/shard-${shard_idx}-time.log"
        local start_ms
        local end_ms
        local max_rss_kb=0
        start_ms=$(date +%s%3N)
        ./.lake/build/bin/ten-tile-shard-report-gen \
            --shard="$shard_idx" --num-shards="$NUM_SHARDS" \
            "$output_file" > >(tee "$OUTPUT_DIR/shard-${shard_idx}-output.log") &
        local pid=$!
        while kill -0 "$pid" 2>/dev/null; do
            if [[ -r "/proc/$pid/status" ]]; then
                local rss_kb
                rss_kb=$(awk '/^VmRSS:/{print $2}' "/proc/$pid/status")
                if [[ "${rss_kb:-0}" -gt "$max_rss_kb" ]]; then
                    max_rss_kb=$rss_kb
                fi
            fi
            sleep 1
        done
        wait "$pid"
        local status=$?
        end_ms=$(date +%s%3N)
        printf 'elapsed_ms=%s\nmax_rss_kb=%s\nexit_status=%s\n' \
            "$((end_ms - start_ms))" "$max_rss_kb" "$status" | tee "$time_log"
        return "$status"
    fi
}

# Run all shards sequentially
for ((i=0; i<NUM_SHARDS; i++)); do
    run_shard "$i"
done

echo ""
echo "=== Sharded execution completed ===" >&2
echo "Results in: $OUTPUT_DIR"
ls -lh "$OUTPUT_DIR"/shard-*.txt
