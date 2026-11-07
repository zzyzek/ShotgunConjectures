#!/usr/bin/env bash
# Compile this repo's Mathlib-based library lib/OpenProblemsLib/*.lean to
# .olean/.ilean files under lib/build/, in dependency order, so that
# `import OpenProblemsLib.Korselt` resolves through LEAN_PATH (the check
# script tools/leancheck-mathlib.sh puts lib/build first on LEAN_PATH).
# Same limits as the check script: one of its 3 machine-wide slots,
# 6 GB, nice 19, 900 s per module.
#
# Usage: tools/buildlib.sh            (rebuild modules whose source is newer)
#        tools/buildlib.sh --force    (rebuild everything)
#
set -u
PROJ="${MATHLIB_PROJECT:-$HOME/claude/SubexponentialDeterministicFactoring}"
REPO="$(cd "$(dirname "$0")/.." && pwd)"
LIB="$REPO/lib"
OUT="$LIB/build"
LP="$OUT:"
for d in "$PROJ"/.lake/packages/*; do LP="$LP$d/.lake/build/lib/lean:"; done
SLOTS=3
LOCKDIR="$HOME/.cache/open-problems-locks"; mkdir -p "$LOCKDIR"
FORCE=0; [ "${1:-}" = "--force" ] && FORCE=1

# Dependency order: a module may import only modules listed before it.
# PNTPlus/* is the vendored PrimeNumberTheoremAnd closure (lib/PNTPlus/README.md);
# it is built first, OpenProblemsLib/* after it.
#
PNTPLUS="Auxiliary MellinCalculus Sobolev Fourier Mathlib/Analysis/SpecialFunctions/Log/Basic Rectangle ResidueCalcOnRectangles EulerMaclaurin ZetaBounds ZetaConj Mathlib/Algebra/Notation/Support SmoothExistence MediumPNT StrongPNT Defs Mathlib/Analysis/Asymptotics/Asymptotics Wiener Consequences"
MODULES="PowMod Pratt Fermat Korselt Cipolla SquaredRect ArithFactor D_CombLine R5_Quadratic Dwork DworkLocal DworkEuler DworkMultinomial ShevelevFactorial QSeries BernoulliDen ModularSums DworkLocalPoly Digits10 Misc ShortIntervalPrimes LRAT AutomaticMod HannaMod4"

compile() {
  local src="$1" olean="$2" ilean="$3"
  env LEAN_PATH="$LP" systemd-run --user --scope -q -p MemoryMax=6G -p MemorySwapMax=0 \
    nice -n 19 timeout 900 lean -R "$LIB" -o "$olean" -i "$ilean" "$src" 2>&1
}

# Take one slot for the whole build (first free one, else wait on a random one).
#
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

status=0
mkdir -p "$OUT/OpenProblemsLib"
rebuilt=0
for pm in $(for m in $PNTPLUS; do echo "PNTPlus/$m"; done) $(for m in $MODULES; do echo "OpenProblemsLib/$m"; done); do
  m="${pm//\//.}"
  src="$LIB/$pm.lean"
  olean="$OUT/$pm.olean"
  ilean="$OUT/$pm.ilean"
  mkdir -p "$(dirname "$olean")"
  if [ $FORCE -eq 0 ] && [ $rebuilt -eq 0 ] && [ -f "$olean" ] && [ "$olean" -nt "$src" ]; then
    echo "up to date $m"
    continue
  fi
  # Once one module is rebuilt, rebuild all later ones (they may import it).
  #
  rebuilt=1
  out=$(compile "$src" "$olean" "$ilean"); rc=$?
  if [ $rc -eq 0 ] && ! grep -q 'error' <<<"$out"; then
    echo "built $m"
    [ -n "$out" ] && sed 's/^/   /' <<<"$out" | head -20
  else
    echo "FAIL $m (exit $rc)"
    sed 's/^/   /' <<<"$out" | head -60
    rm -f "$olean" "$ilean"
    status=1
    break
  fi
done

# Root module importing all parts.
#
if [ $status -eq 0 ]; then
  src="$LIB/OpenProblemsLib.lean"
  out=$(compile "$src" "$OUT/OpenProblemsLib.olean" "$OUT/OpenProblemsLib.ilean"); rc=$?
  if [ $rc -eq 0 ] && ! grep -q 'error' <<<"$out"; then echo "built OpenProblemsLib"
  else echo "FAIL OpenProblemsLib (exit $rc)"; sed 's/^/   /' <<<"$out" | head -40; status=1; fi
fi
flock -u 9; exec 9>&-
exit $status
