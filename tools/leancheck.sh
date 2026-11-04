#!/usr/bin/env bash
# Check Lean files one at a time, machine-wide: a lock serialises every
# caller (agents included), each run is capped at 1 GB, nice 19, 300 s.
# Prints "OK <file>" plus the axioms of every theorem, or the errors.
#
# Usage: tools/leancheck.sh OEIS/A100682/A100682.lean [more.lean ...]
#
set -u
LOCK="$HOME/.cache/open-problems-locks/leancheck.lock"; mkdir -p "$(dirname "$LOCK")"
status=0
for f in "$@"; do
  tmp="${f%.lean}.axioms.lean"
  cp "$f" "$tmp"
  grep -oE '^(theorem|lemma) [A-Za-z0-9_.]+' "$f" | awk '{print "#print axioms " $2}' >> "$tmp"
  out=$(flock "$LOCK" systemd-run --user --scope -q -p MemoryMax=1G -p MemorySwapMax=0 \
        nice -n 19 timeout 300 lean "$tmp" 2>&1)
  rc=$?
  rm -f "$tmp"
  if [ $rc -eq 0 ] && ! grep -q 'error' <<<"$out" && ! grep -q 'sorry' <<<"$out"; then
    echo "OK $f"
    grep -E 'axioms|does not depend|warning' <<<"$out" | sed 's/^/   /'
  else
    echo "FAIL $f (exit $rc)"
    sed 's/^/   /' <<<"$out" | head -40
    status=1
  fi
done
exit $status
