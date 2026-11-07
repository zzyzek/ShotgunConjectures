#!/usr/bin/env bash
# Compile the E13.1 LRAT modules (NT/E13.1/lrat/E13Lrat/*.lean) to .olean files under
# lib/build/E13Lrat/, so that NT/E13.1/E13_1_lrat.lean (checked by tools/leancheck-mathlib.sh,
# which puts lib/build on LEAN_PATH) can import them. Compiling a module is its kernel check.
# Same limits as tools/buildlib.sh: one of the 3 machine-wide slots, 6 GB, nice 19, 900 s
# per module. Run from anywhere; data paths in the modules are relative to the repo root.
#
# Usage: NT/E13.1/lrat/build.sh Cnf Store2 F2 A00 A01 ...   (module names, in dependency order)
#
set -u
PROJ="${MATHLIB_PROJECT:-$HOME/claude/SubexponentialDeterministicFactoring}"
REPO="$(cd "$(dirname "$0")/../../.." && pwd)"
SRC="$REPO/NT/E13.1/lrat"
OUT="$REPO/lib/build"
LP="$OUT:"
for d in "$PROJ"/.lake/packages/*; do LP="$LP$d/.lake/build/lib/lean:"; done
SLOTS=3
LOCKDIR="$HOME/.cache/open-problems-locks"; mkdir -p "$LOCKDIR"
cd "$REPO"
got=0
for i in $(seq 1 $SLOTS); do
  exec 9>"$LOCKDIR/open-problems-mathlib-$i.lock"
  if flock -n 9; then got=1; break; fi
done
if [ $got -eq 0 ]; then
  i=$(( (RANDOM % SLOTS) + 1 ))
  exec 9>"$LOCKDIR/open-problems-mathlib-$i.lock"
  flock 9
fi
mkdir -p "$OUT/E13Lrat"
status=0
for m in "$@"; do
  t0=$(date +%s)
  out=$(env LEAN_PATH="$LP" systemd-run --user --scope -q -p MemoryMax=6G -p MemorySwapMax=0 \
    nice -n 19 timeout 900 /usr/bin/time -f "peak %M KB" lean -R "$SRC" \
    -o "$OUT/E13Lrat/$m.olean" -i "$OUT/E13Lrat/$m.ilean" "$SRC/E13Lrat/$m.lean" 2>&1)
  rc=$?
  t1=$(date +%s)
  if [ $rc -eq 0 ] && ! grep -q 'error' <<<"$out"; then
    echo "built E13Lrat.$m $((t1 - t0)) s $(grep -o 'peak [0-9]* KB' <<<"$out")"
    grep -v '^peak' <<<"$out" | sed 's/^/   /' | head -20
  else
    echo "FAIL E13Lrat.$m (exit $rc) $((t1 - t0)) s"
    sed 's/^/   /' <<<"$out" | head -40
    rm -f "$OUT/E13Lrat/$m.olean" "$OUT/E13Lrat/$m.ilean"
    status=1
    break
  fi
done
flock -u 9; exec 9>&-
exit $status
