#!/usr/bin/env bash
set -euo pipefail

# Benchmark runner for oprf_example.
#
# Runs (once):
#   nargo compile
#   bb write_vk -b target/oprf_example.json -t noir-recursive -o out/vk_recursive
#   bb write_vk -b target/oprf_example.json -t evm            -o out/vk_evm
#
# Then repeats N times:
#   nargo execute
#   bb prove ... -t noir-recursive
#   bb prove ... -t evm
#
# Output:
#   - out/bench_times.csv (per-run timings in ms)
#   - printed summary (mean/min/max/stdev)

RUNS="${RUNS:-10}"
CSV_OUT="${CSV_OUT:-out/bench_times.csv}"
BB_SLOW_LOW_MEMORY="${BB_SLOW_LOW_MEMORY:-0}"
BB_STORAGE_BUDGET="${BB_STORAGE_BUDGET:-}"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$script_dir"

require_cmd() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "error: missing required command '$1' in PATH" >&2
    exit 1
  fi
}

now_ns() {
  date +%s%N
}

time_ms() {
  # Usage: time_ms <cmd> [args...]
  local start_ns end_ns dur_ns
  start_ns="$(now_ns)"
  # Important: this function is typically invoked via command substitution
  # (e.g. ms="$(time_ms bb prove ...)"). If the benchmarked command prints
  # to stdout, it would get captured and corrupt the timing value and CSV.
  # Redirect stdout to stderr so only the numeric duration is captured.
  "$@" 1>&2
  end_ns="$(now_ns)"
  dur_ns=$((end_ns - start_ns))
  echo $((dur_ns / 1000000))
}

bb_prove() {
  # Usage: bb_prove <verifier_target> <vk_path>
  local verifier_target="$1"
  local vk_path="$2"

  local -a cmd
  cmd=(bb prove -b target/oprf_example.json -w target/oprf_example.gz -k "$vk_path" -t "$verifier_target")
  if [[ "$BB_SLOW_LOW_MEMORY" == "1" ]]; then
    cmd+=(--slow_low_memory)
  fi
  if [[ -n "$BB_STORAGE_BUDGET" ]]; then
    cmd+=(--storage_budget "$BB_STORAGE_BUDGET")
  fi

  "${cmd[@]}"
}

append_csv() {
  local iteration="$1"
  local phase="$2"
  local ms="$3"
  echo "${iteration},${phase},${ms}" >> "$CSV_OUT"
}

require_cmd nargo
require_cmd bb

if ! [[ "$RUNS" =~ ^[0-9]+$ ]] || [[ "$RUNS" -le 0 ]]; then
  echo "error: RUNS must be a positive integer (got '$RUNS')" >&2
  exit 1
fi
if ! [[ "$BB_SLOW_LOW_MEMORY" =~ ^[01]$ ]]; then
  echo "error: BB_SLOW_LOW_MEMORY must be 0 or 1 (got '$BB_SLOW_LOW_MEMORY')" >&2
  exit 1
fi

mkdir -p out

echo "iteration,phase,ms" > "$CSV_OUT"

echo "== One-off setup =="
ms_compile="$(time_ms nargo compile)" || exit $?
append_csv 0 compile "$ms_compile"

echo "Writing verification keys..."
ms_vk_recursive="$(time_ms bb write_vk -b target/oprf_example.json -t noir-recursive -o out/vk_recursive)" || exit $?
append_csv 0 write_vk_recursive "$ms_vk_recursive"

ms_vk_evm="$(time_ms bb write_vk -b target/oprf_example.json -t evm -o out/vk_evm)" || exit $?
append_csv 0 write_vk_evm "$ms_vk_evm"

echo "== Benchmark (${RUNS}x) =="
for ((i = 1; i <= RUNS; i++)); do
  echo "run ${i}/${RUNS}: nargo execute"
  ms_execute="$(time_ms nargo execute)" || exit $?
  append_csv "$i" execute "$ms_execute"

  echo "run ${i}/${RUNS}: bb prove (noir-recursive)"
  ms_prove_recursive="$(time_ms bb_prove noir-recursive out/vk_recursive/vk)" || exit $?
  append_csv "$i" prove_noir_recursive "$ms_prove_recursive"

  echo "run ${i}/${RUNS}: bb prove (evm)"
  ms_prove_evm="$(time_ms bb_prove evm out/vk_evm/vk)" || exit $?
  append_csv "$i" prove_evm "$ms_prove_evm"
done

echo ""
echo "== Summary (ms) =="

awk_summary() {
  awk -F, '
    function min(a,b){ return (a=="" || b<a) ? b : a }
    function max(a,b){ return (a=="" || b>a) ? b : a }
    NR==1 { next }
    {
      iter = $1
      phase = $2
      ms = $3 + 0
      if (iter == 0) {
        oneoff[phase] = ms
        next
      }
      count[phase] += 1
      sum[phase] += ms
      sumsq[phase] += (ms * ms)
      minv[phase] = min(minv[phase], ms)
      maxv[phase] = max(maxv[phase], ms)
    }
    END {
      print "One-off:";
      for (p in oneoff) {
        printf "  %-22s %10.2f\n", p, oneoff[p]
      }
      print "";
      print "Repeated:";
      for (p in count) {
        mean = sum[p] / count[p]
        var = (sumsq[p] / count[p]) - (mean * mean)
        if (var < 0) var = 0
        stdev = sqrt(var)
        printf "  %-22s mean=%10.2f  min=%10.2f  max=%10.2f  stdev=%10.2f  n=%d\n", p, mean, minv[p], maxv[p], stdev, count[p]
      }
    }
  ' "$CSV_OUT"
}

awk_summary

echo ""
echo "Wrote: $CSV_OUT"