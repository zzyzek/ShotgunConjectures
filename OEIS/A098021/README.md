# OEIS A098021: former and current definitions agree

**Source.** OEIS [A098021](https://oeis.org/A098021), current name (C. Kimberling, adopted by
N. J. A. Sloane 2016-01-30, rev. #25): "Positions of 0's in the zero-one sequence
[n*r+2*r]-[n*r]-[2*r], where r=sqrt(2) and [ ]=floor; see A187967." Former definition
(R. L. Bagula 2004, [history](https://oeis.org/history?seq=A098021)): f(n) = n·√2 mod 1,
g(x) = −1 on [0,1/3], 0 on (1/3,2/3], 1 on (2/3,1]; n is a term when
f(n+2) − 2f(n+1) + f(n) − g(f(n+1)) = 0. Kimberling's 2011 comment was the conjecture that the two
agree. (OEIS text, CC BY-SA 4.0.)

**Reading.** The former FORMULA line wrote "g(x)=1 if 1/3<x<=1", an evident typo for 2/3 (the
Mathematica program uses 2/3); with the cases tested in order both give the same g.

**Result.** The definitions agree for every integer n; proved in Lean 4 + Mathlib.

**Argument.** Let x = frac((n+1)√2) and α = √2 − 1 ≈ 0.414. Then frac(n√2) = x − α + [x < α] and
frac((n+2)√2) = x + α − [x ≥ 1 − α], so the second difference is [x < α] − [x ≥ 1 − α].
- x < α: difference 1, but g(x) ∈ {−1, 0}.
- x ≥ 1 − α ≈ 0.586: difference −1, but g(x) ∈ {0, 1}.
- α ≤ x < 1 − α: difference 0 = g(x).
So the old condition holds iff α ≤ x < 1 − α, i.e. iff frac(n√2) < 1 − 2α = 3 − 2√2. The new
condition [n√2 + 2√2] − [n√2] − 2 = 0 holds iff frac(n√2) + 2√2 < 3, the same inequality.
Irrationality of √2 is not used.

**Evidence.**
- Lean (Mathlib): [`A098021_mathlib.lean`](A098021_mathlib.lean).
  - `A098021_key`: for every real y, the second-difference condition at y equals
    ⌊y + 2√2⌋ − ⌊y⌋ − ⌊2√2⌋ = 0.
  - `A098021_defs_agree (n : ℤ)`: `A098021_old n ↔ A098021_new n`.
  - `A098021_old_eq_new`: `Nat.nth (0 < n ∧ old) = Nat.nth (0 < n ∧ new)` (the two sequences).
  Check: `tools/leancheck-mathlib.sh OEIS/A098021/A098021_mathlib.lean` → OK, no warnings.
  Axioms: `propext, Classical.choice, Quot.sound`. No `sorry`, no `native_decide`.
- [`certificate/check_A098021.py`](certificate/check_A098021.py): both definitions agree for
  1 ≤ n < 20000, the listed terms match, and every term found equals 3i + 2⌊i√2⌋.
- Outside Lean: none for the agreement. The terms and the formula 3n + 2⌊n√2⌋ are checked only by
  the script.

**Review level.** `lean-proof` (re-derived; the whole statement is proved in Lean).

**Prior art.** Known in effect: the entry adopted the new definition in 2016 without a recorded
proof that it matches the old one; the argument is immediate. google-deepmind/formal-conjectures has
no `FormalConjectures/OEIS/98021.lean`, and otoi-lab/oeis-lean-proofs has no file for it (checked
2026-11-05). (Prior-art review 2026-11-05.)
