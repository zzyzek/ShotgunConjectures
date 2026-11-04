#!/usr/bin/env bash
# Check Lean files that import Mathlib, using a prebuilt Mathlib for Lean
# 4.35.0 read-only through LEAN_PATH (no lake, nothing is rebuilt). At most
# SLOTS runs at once machine-wide, each capped at 6 GB, nice 19, 900 s.
# Prints "OK <file>" plus the axioms of every theorem, or the errors.
#
# Usage: tools/leancheck-mathlib.sh COM/C003/C003.lean [more.lean ...]
# MATHLIB_PROJECT: a lake project whose .lake/packages hold built Mathlib.
#
set -u
PROJ="${MATHLIB_PROJECT:-$HOME/claude/SubexponentialDeterministicFactoring}"
# lib/build holds this repo's own compiled library (tools/buildlib.sh).
#
REPO="$(cd "$(dirname "$0")/.." && pwd)"
LP="$REPO/lib/build:"
for d in "$PROJ"/.lake/packages/*; do LP="$LP$d/.lake/build/lib/lean:"; done
SLOTS=3
LOCKDIR="$HOME/.cache/open-problems-locks"; mkdir -p "$LOCKDIR"
status=0
for f in "$@"; do
  tmp="${f%.lean}.axioms.lean"
  cp "$f" "$tmp"
  grep -oE '^(theorem|lemma) [A-Za-z0-9_.'"'"']+' "$f" | awk '{print "#print axioms " $2}' >> "$tmp"

  # Take the first free slot; if none is free, wait on a random one.
  #
  run() {
    env LEAN_PATH="$LP" systemd-run --user --scope -q -p MemoryMax=6G -p MemorySwapMax=0 \
      nice -n 19 timeout 900 lean "$tmp" 2>&1
  }
  out=""; rc=255; got=0
  for i in $(seq 1 $SLOTS); do
    exec 9>"$LOCKDIR/open-problems-mathlib-$i.lock"
    if flock -n 9; then got=1; out=$(run); rc=$?; flock -u 9; break; fi
  done
  if [ $got -eq 0 ]; then
    i=$(( (RANDOM % SLOTS) + 1 ))
    exec 9>"$LOCKDIR/open-problems-mathlib-$i.lock"
    flock 9; out=$(run); rc=$?; flock -u 9
  fi
  exec 9>&-
  rm -f "$tmp"
  if [ $rc -eq 0 ] && ! grep -q 'error' <<<"$out" && ! grep -q 'sorry' <<<"$out"; then
    echo "OK $f"
    grep -E 'axioms|does not depend|warning' <<<"$out" | sed 's/^/   /'
  else
    echo "FAIL $f (exit $rc)"
    sed 's/^/   /' <<<"$out" | head -60
    status=1
  fi
done
exit $status
