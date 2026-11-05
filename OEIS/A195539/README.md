# OEIS A195539: numerators of Pythagorean approximations to √8 satisfy b(n) = 34b(n−2) − b(n−4)

**Source.** OEIS [A195539](https://oeis.org/A195539) (offset 1): numerators b(n) of Pythagorean approximations
b(n)/a(n) to √8: 12, 35, 408, 1189, 13860, ... Conjecture (R. J. Mathar, Sep 2011): "a(n) = +34*a(n-2)
-a(n-4) with a(2*n+1) = A000129(4*n+4), a(2*n) = A046176(n+1)." (OEIS text, CC BY-SA 4.0; still a conjecture
on 2026-11-05, revision #10.)

**Reading.** Same construction as [A195538](../A195538/README.md) (P. J. C. Moses' program): b(n) is the
numerator of (p² − q²)/(2pq) in lowest terms, p/q the n-term convergent of 3 + 2√2. A000129 = Pell numbers
(offset 0, by their recurrence); A046176 (offset 1) = positive m such that m² is a hexagonal number h(2h − 1),
in increasing order (1, 35, 1189, ...).

**Result.** True (recurrence and both bisection formulas, the odd one for n ≥ 0 and the even one for n ≥ 1).

**Argument.** With the notation of A195538 ((X_k, W_k) solutions of X² − 8W² = 1, U = X + 2W, V = X + 3W),
the lowest-terms computation gives b(2k+1) = 4V(U+2V) and b(2k+2) = (U+5V)² − V². The addition formula
X_(a+b) = X_aX_b + 8W_aW_b, W_(a+b) = X_aW_b + W_aX_b turns these into b(2k+1) = 2W_(2k+2) and
b(2k+2) = W_(2k+3). Pell(2j) = 2W_j and Pell(2j+1) = X_j + 2W_j (induction), so b(2n+1) = Pell(4n+4).
m² = h(2h − 1) ⇔ (4h − 1)² − 8m² = 1, so (4h − 1, m) = (X_k, W_k); X_k ≡ 1 (mod 4) for even k and 3 for
odd k, so the hexagonal-square indices are W_(2j+1), j ≥ 0, and A046176(n+1) = W_(2n+1) = b(2n). The
recurrence b(n) = 34b(n−2) − b(n−4) follows since both bisections are W at indices in an arithmetic
progression of step 2 (a polynomial identity in X_k, W_k).

**Evidence.**
- Lean (Mathlib): [`A195539_mathlib.lean`](A195539_mathlib.lean), `A195539_main`: (1) b(1..15) are the printed
  terms; (2) ∀ n ≥ 5, b(n) = 34b(n−2) − b(n−4); (3) ∀ n, b(2n+1) = A000129(4n+4); (4) ∀ n ≥ 1,
  b(2n) = A046176(n+1). b(n) is `Rat.num` of the same rational as in A195538; A046176 is `Nat.nth` of its
  defining set. Lemmas: `A195539_b_odd`, `A195539_b_even`, `A195539_XW_add`, `A195539_pell`, `A195539_S3_iff`,
  `A195539_classify`. Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py` (shared with A195538): printed terms, recurrence for n ≤ 60, bisections against Pell
  numbers and brute-force A046176.
- Outside Lean: only the identification of Mathematica's FromContinuedFraction with the recurrence
  convergent (as for A195538).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05: no proof in the entry, A195500 or the web; not in
google-deepmind/formal-conjectures.
