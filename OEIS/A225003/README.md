# OEIS A225003 (dead): a(n) = A047332(n) for n ≥ 2

**Source.** OEIS [A225003](https://oeis.org/history?seq=A225003) (T. D. Noe, 2013, from
M. B. Nathanson, On the fractional parts of roots of positive real numbers, Amer. Math. Monthly 120
(2013) 409–429): "Floor(1/f(x^(1/n))) for x = e^(5/7), where f computes the fractional part",
offset 1, data 23, 2, 3, 5, 6, 7, .... Comment: "Conjecture: a(n) = A047332(n), n>1. - R. J. Mathar,
Apr 28 2013". Since 2017 the entry is "Duplicate of A047332" (dead, A. Zabolotskiy).
[A047332](https://oeis.org/A047332): numbers congruent to {0, 2, 3, 5, 6} mod 7, offset 1, with
FORMULA a(n) = floor((7n−3)/5). (OEIS text, CC BY-SA 4.0.)

**Result.** True: a(n) = floor((7n−3)/5) = A047332(n) for every n ≥ 2 (a(1) = 23); proved in
Lean 4 + Mathlib.

**Argument.** Let t = 5/(7n) ≤ 5/14 and q = floor((7n−3)/5), so 5q + 3 ≤ 7n ≤ 5q + 7, i.e.
qt ≤ 1 − 3t/5 and (q+1)t ≥ 1 − 2t/5. Taylor bounds give
1 + t + t²/2 ≤ e^t ≤ 1 + t + t²/2 + 2t³/9, so 1 < e^t < 2 and frac(e^t) = d = e^t − 1. Then
q·d ≤ (1 − 3t/5)(1 + t/2 + 2t²/9) ≤ 1 and (q+1)·d ≥ (1 − 2t/5)(1 + t/2) = 1 + t/10 − t²/5 > 1,
so q ≤ 1/d < q + 1. The values of floor((7n−3)/5) for n ≥ 1 are strictly increasing and are exactly
the numbers ≡ 0, 2, 3, 5, 6 mod 7, so they enumerate A047332.

**Evidence.**
- Lean (Mathlib): [`A225003_mathlib.lean`](A225003_mathlib.lean). `A225003 n` is
  ⌊1 / Int.fract (exp(5/7) ^ (1/n))⌋ (real power), `A047332 n` is `Nat.nth` of the residue
  predicate at n − 1.
  - `A047332_formula`: n ≥ 1 → A047332 n = (7n − 3)/5.
  - `A225003_floor_exp`: n ≥ 2 → ⌊1 / frac(e^(5/(7n)))⌋ = (7n − 3)/5.
  - `A225003_formula`: n ≥ 2 → A225003 n = (7n − 3)/5.
  - `A225003_conjecture`: n ≥ 2 → A225003 n = A047332 n.
  Check: `tools/leancheck-mathlib.sh OEIS/A225003/A225003_mathlib.lean` → OK, no warnings.
  Axioms: `propext, Classical.choice, Quot.sound`. No `sorry`, no `native_decide`.
- [`certificate/check_A225003.py`](certificate/check_A225003.py): 80-digit decimals reproduce the
  67 listed terms and a(n) = floor((7n−3)/5) = A047332(n) for 2 ≤ n ≤ 5000.
- Outside Lean: none for the conjecture. The listed terms are checked only by the script.

**Review level.** `lean-proof` (re-derived; the whole statement is proved in Lean).

**Prior art.** Known: the entry was marked a duplicate of A047332 in 2017 (A. Zabolotskiy), which
implies the conjecture, but no proof was recorded; the estimate is the standard expansion
1/(e^t − 1) = 1/t − 1/2 + t/12 − .... google-deepmind/formal-conjectures has no
`FormalConjectures/OEIS/225003.lean`, and otoi-lab/oeis-lean-proofs has no file for it (checked
2026-11-05). (Prior-art review 2026-11-05.)
