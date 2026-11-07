# OEIS A060298: limits of a(2n)/10^n and a(2n-1)/10^n

**Source.** [A060298](https://oeis.org/A060298), number of powers x^y (x, y > 1) with n digits. Conjectures of
R. G. Wilson v (Aug 29 2012): lim a(2n)/10^n = 1 - 1/sqrt(10) and lim a(2n-1)/10^n = 1/sqrt(10) - 1/10, followed by
"These follow from the Formula. - Robert Israel, Apr 29 2020" (formula a(n) = sum_y (ceil(10^(n/y)) -
ceil(10^((n-1)/y)))). (OEIS text, CC BY-SA 4.0, revision #67 of Oct 16 2023, checked 2026-11-07.)

**Reading.** Powers are counted as pairs (x, y): 64 = 2^6 = 4^3 = 8^2 counts three times. This reproduces the data
(a(2) = 12, certificate/check.py) and Israel's formula.

**Result.** True (known: Israel's remark in the entry, no written proof there).

**Argument.** Pairs with y >= 3 and x^y < 10^N have x < 3^N (27^N > 10^N) and y < 4N (16^N > 10^N): at most
4N 3^N = o(10^(N/2)). Pairs with y = 2 number isqrt(10^N - 1) - isqrt(10^(N-1) - 1) = r^N - r^(N-1) + O(1),
r = sqrt(10). So a(N)/r^N -> 1 - 1/r; N = 2n gives 1 - 1/sqrt(10), N = 2n+1 divided by r gives 1/sqrt(10) - 1/10.

**Evidence.**
- Lean (Mathlib): [`A060298_mathlib.lean`](A060298_mathlib.lean). `a N` counts pairs (x, y) in [0,10^N)^2 with
  x, y >= 2 and 10^(N-1) <= x^y < 10^N. Main theorems `A060298.A060298_even` (a(2n)/10^n -> 1 - 1/sqrt 10) and
  `A060298.A060298_odd` (a(2n+1)/10^(n+1) -> 1/sqrt 10 - 1/10). Axioms propext, Classical.choice, Quot.sound.
- `certificate/check.py`: the pair count reproduces the first 15 data terms.
- Outside Lean: none (agreement of the definition with the data by the script only).

**Review level.** `lean-proof`.

**Prior art.** Settled in the entry by R. Israel's 2020 remark (no proof written). Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (checked 2026-11-07).
