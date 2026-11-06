# OEIS A109926: "a(n+15) == 0 (mod 30) for n > 4" is false as printed; the mod 3 and mod 15 claims are out of reach

**Source.** [A109926](https://oeis.org/A109926) (offset 0, keywords hard, more): least k such that k - 2^r is prime
for n values of r. Data a(0..20) = 1, 3, 4, 15, 21, 45, 75, 465, ..., 53999715, 2282745465. Comments: T. D. Noe
(2005) "It appears that 3 and 5 divide a(n) for n>4"; Robert G. Wilson v (Jul 21 2005) "Conjecture: a(n)==0
(mod 3) for n > 2" and "Conjecture: a(n+15)==0 (mod 30) for n > 4". (OEIS text, CC BY-SA 4.0, checked
2026-11-06.)

**Reading.** "For n values of r" means exactly n (the entry's programs count exactly; certificate/check.py
reproduces a(0..12) this way); r >= 0 and k - 2^r must be a prime (so 2^r < k).

**Result.**
- The second conjecture is false as printed: a(m) is odd for every m >= 3, so a(n+15) is never divisible by 30;
  for instance a(20) = 2282745465 = 15 (mod 30). All data terms a(5..20) are 15 (mod 30), so the intended
  statement is presumably "a(n)+15 == 0 (mod 30)", i.e. a(n) = 15 (mod 30), for n > 4.
- The odd part of that corrected statement holds for all n >= 3 (whenever a(n) exists). The parts "3 | a(n)" and
  "5 | a(n)" for all large n are not attempted: they assert that the least k with exactly n prime values k - 2^r is
  a multiple of 3 (and 5) for every n, which needs control of primes among k - 2^r for all k below a(n). It also
  presupposes that every count n is attained, which is not known (Erdős 1950 showed the count is unbounded). This
  is famous-strength in the sense of the scan rules: no method proves such statements.

**Argument.** If k is even and r >= 1, then k - 2^r is even, so it is prime only if k - 2^r = 2, i.e. 2^r = k - 2,
which fixes r. With r = 0 this gives at most 2 representations. So k with at least 3 representations is odd.

**Evidence.**
- Lean (Mathlib): [`A109926_mathlib.lean`](A109926_mathlib.lean). Definitions: `repSet k`, `reps k` (number of r
  with 2^r < k and k - 2^r prime). Theorems: `odd_of_three_le` (reps k >= 3 implies k odd),
  `A109926_not_dvd_30` (for m >= 3 the least k with reps k = m is not divisible by 30).
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings. Axioms: propext, Classical.choice, Quot.sound.
- [`certificate/a20.gp`](certificate/a20.gp), output [`certificate/a20.out`](certificate/a20.out): PARI/gp
  (exit 0, no errors) finds exactly 20 primes among 2282745465 - 2^r, with a small factor for each other r, and
  lists the data mod 30. [`certificate/check.py`](certificate/check.py): reproduces a(0..12) from the definition.
- Outside Lean: existence of a(20) (that 2282745465 has exactly 20 representations is by PARI; its minimality is
  the entry's, D. Johnson 2009). Not needed for the parity theorem, only to name an index where the printed
  conjecture visibly fails.

**Review level.** `lean-proof` (parity), `rechecked` (a(20) witness).

**Prior art.** Checked 2026-11-06. Entry and history: both conjectures still stated (Jul 21 2005), no proof or
correction. Web search: Erdős (1950) proved the representation count of n = p + 2^k unbounded; nothing on exact
counts being attained or on residues of first occurrences. Not in google-deepmind/formal-conjectures (no 109926
file in the tree at HEAD) or otoi-lab/oeis-lean-proofs.
