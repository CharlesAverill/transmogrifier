#!/usr/bin/env bash
# Session example demo. Run from the repository root.
set -uo pipefail

DIR="examples/session"
SECRET='s3cr3t-handshake-key'

enc() {
  python3 -c '
import sys
w = sys.argv[1]; tok = sys.argv[2].encode()
bad = b"z" * len(tok)
o = bytearray()
for c in w:
    if c == "a":   o += b"a" + bytes([len(tok)]) + tok
    elif c == "b": o += b"a" + bytes([len(bad)]) + bad
    else:          o += c.encode()
sys.stdout.buffer.write(o)' "$1" "$SECRET"
}

overflow() {
  python3 -c 'import sys; sys.stdout.buffer.write(b"a" + bytes([200]) + b"A"*1024)'
}

hdr() { printf '\n--- %s ---\n' "$*"; }

[ -f "$DIR/session_legacy.c" ] || { echo "run from repository root"; exit 1; }

OUT="$DIR/out"
rm -rf "$OUT/*"; mkdir -p "$OUT"
LEGACY="$OUT/session_legacy"
LEGACY_ASAN="$OUT/legacy_asan"
MODERN="$OUT/session"
MODERN_ASAN="$OUT/session_asan"
GEN_C="$OUT/session.c"
GEN_H="$OUT/session.h"
for t in ccomp dune python3; do
  command -v "$t" >/dev/null 2>&1 || { echo "missing: $t"; exit 1; }
done

asan_cc=""
for c in ccomp gcc clang cc; do
  if command -v "$c" >/dev/null 2>&1 \
     && echo 'int main(void){return 0;}' \
        | "$c" -fsanitize=address -x c - -o "$OUT/.probe" 2>/dev/null; then
    asan_cc="$c"; break
  fi
done

gcc -O3 -o "$LEGACY" "$DIR/session_legacy.c" || exit 1

hdr "1. legacy normal operation"
enc harkr | "$LEGACY"

hdr "2. legacy memory error"
# An oversized AUTH token field overflows the stack scratch buffer in
# slurp_token, before the phase gate runs.
if [ -n "$asan_cc" ]; then
  "$asan_cc" -fsanitize=address -g -O0 -o "$LEGACY_ASAN" "$DIR/session_legacy.c"
  overflow | "$LEGACY_ASAN" 2>&1 \
    | grep -E 'ERROR|stack-buffer-overflow|slurp_token|handle_auth|#[0-9]+ ' | head -n 8
else
  echo "(no ASan-capable compiler; running uninstrumented)"
  overflow | "$LEGACY"; echo "exit $?"
fi

hdr "3. learner"
SESSION_LEGACY="$(pwd)/$LEGACY" \
SESSION_OUT_C="$(pwd)/$GEN_C" \
SESSION_OUT_H="$(pwd)/$GEN_H" \
MEALY_H_TEMPLATE="include/mealy.h.in" \
  dune exec "$DIR/learn_compile.exe" 2>&1 | grep -E 'Accuracy|Wrote|states'

hdr "4. compile"
ccomp -O3 -o "$MODERN" "$DIR/session_modern.c" "$GEN_C" -I "$OUT" || exit 1

hdr "5. modern: normal operation"
enc harkr | "$MODERN"

echo
printf '%-8s %-34s %-34s %s\n' "Token" "Legacy Response" "Modern Response" "Matching"
for w in h a r x ha har hark harkr rrr hax kkk harxr harrr b hb hba hbr hbar; do
  L=$(enc "$w" | "$LEGACY" 2>/dev/null | tr '\n' ' ')
  C=$(enc "$w" | "$MODERN" 2>/dev/null | tr '\n' ' ')
  [ "$L" = "$C" ] && s=ok || s=DIFF
  printf '%-8s %-34s %-34s %s\n' "$w" "$L" "$C" "$s"
done

hdr "6. modern: no bug"
if [ -n "$asan_cc" ]; then
  "$asan_cc" -fsanitize=address -g -O0 -o "$MODERN_ASAN" \
    "$DIR/session_modern.c" "$GEN_C" -I "$OUT"
  overflow | "$MODERN_ASAN" 2>&1 \
    | grep -E 'ERROR|stack-buffer-overflow|slurp_token|handle_auth|#[0-9]+ ' | head -n 8
else
  overflow | "$MODERN"; echo "exit $?"
fi

hdr "7. performance benchmark" 
WORKLOAD_SIZE=10000
echo "Generating payload with ${WORKLOAD_SIZE} operations..." 
BENCH_PAYLOAD="$OUT/bench_input.bin" 
enc "$(python3 "-c" "print('harkr' * $WORKLOAD_SIZE)")" > "$BENCH_PAYLOAD" 

time_run_avg() { 
    local binary="$1" 
    python3 "-c" '
import time, subprocess, sys

binary = sys.argv[1]
payload_file = sys.argv[2]
runs = 10000
total_time = 0.0

with open(payload_file, "rb") as f:
    data = f.read()

for _ in range(runs):
    t0 = time.perf_counter()
    p = subprocess.Popen([binary], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = p.communicate(input=data)
    t1 = time.perf_counter()
    total_time += (t1 - t0)

avg_time = total_time / runs
print(f"{avg_time:.6f}")
' "$binary" "$BENCH_PAYLOAD" 
} 

echo "Running legacy binary benchmark (10000 runs)..." 
LEGACY_TIME=$(time_run_avg "$LEGACY") 

echo "Running modern (transmogrified) binary benchmark (10000 runs)..." 
MODERN_TIME=$(time_run_avg "$MODERN") 

echo 
printf '===============================================\n' 
printf '            PERFORMANCE METRICS (AVG)          \n' 
printf '===============================================\n' 
printf '%-20s : %s seconds\n' "Legacy Avg Time" "$LEGACY_TIME" 
printf '%-20s : %s seconds\n' "Modern Avg Time" "$MODERN_TIME" 

python3 "-c" '
import sys
t_legacy = float(sys.argv[1])
t_modern = float(sys.argv[2])
if t_modern > 0:
    speedup = t_legacy / t_modern
    print(f"Performance Change : {speedup:.2f}x speedup")
else:
    print("Modern time too close to zero to safely calculate delta.")
' "$LEGACY_TIME" "$MODERN_TIME" 
printf '===============================================\n' 

rm "-f" "$BENCH_PAYLOAD"
