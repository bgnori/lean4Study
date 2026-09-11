#!/bin/bash
# Measure the compact-key cache on the full ten-tile report.
set -euo pipefail

ROOT_DIR=$(cd "$(dirname "$0")" && pwd)
BINARY="$ROOT_DIR/.lake/build/bin/ten-tile-report-gen"
OUTPUT_PATH=${1:-/tmp/ten-tile-compact-cache-report.txt}
TIME_LOG=${2:-/tmp/ten-tile-compact-cache-time.txt}

if [[ ! -x "$BINARY" ]]; then
  echo "error: build ten-tile-report-gen first" >&2
  exit 1
fi

start_ms=$(date +%s%3N)
"$BINARY" "$OUTPUT_PATH" >"$TIME_LOG.output" 2>&1 &
pid=$!
max_rss_kb=0

while kill -0 "$pid" 2>/dev/null; do
  rss_kb=$(awk '/^VmRSS:/{print $2}' "/proc/$pid/status" 2>/dev/null || printf '0')
  if [[ ${rss_kb:-0} -gt "$max_rss_kb" ]]; then
    max_rss_kb=$rss_kb
  fi
  sleep 1
done

set +e
wait "$pid"
status=$?
set -e
end_ms=$(date +%s%3N)

{
  printf 'exit_status=%s\n' "$status"
  printf 'elapsed_ms=%s\n' "$((end_ms - start_ms))"
  printf 'max_rss_kb=%s\n' "$max_rss_kb"
} | tee "$TIME_LOG"
cat "$TIME_LOG.output"

if [[ "$status" -eq 0 ]]; then
  grep -E '^(tenpaiReports|count:|waitCoreCache|calculationElapsedMs):' "$OUTPUT_PATH"
fi
exit "$status"
