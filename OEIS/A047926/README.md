# OEIS A047926: sorted three-square representations of 3^(2n) (misindexed; reduced to r_3(9^n))

**Source.** OEIS [A047926](https://oeis.org/A047926): a(n) = (3^(n+1) + 2n + 1)/4 (1, 3, 8, 22,
63, ...; offset 0). Comment (Z. Seidov, 2012): "Conjecture: Number of representations of
3^(2n) as a sum a^2 + b^2 + c^2 with 0 < a <= b <= c." It gives the examples a(1) = 3 for 3^2
and a(2) = 3 for 3^4. (OEIS text, CC BY-SA 4.0.)

**Reading.** Let C(N) = #{0 < a ≤ b ≤ c : a² + b² + c² = N}. Then C(9) = 1 and C(81) = 3, but
a(1) = 3 and a(2) = 8. The comment is off by one index, and its own examples contradict the data.
The corrected statement is C(3^(2n+2)) = a(n), or equivalently C(9^n) = (3^n + 2n − 1)/4 for
n ≥ 1. This holds numerically for n ≤ 7.

**Result.** Corrected statement: proved outside Lean from the classical Gauss–Hurwitz formula.
In Lean it is reduced exactly to one missing count (partial).

**Argument.**
1. Descent. If a² + b² + c² = 9M, the squares mod 3 are 0 or 1, so either 3 divides all of a,
   b, c or none of them. The first kind are 3·(solutions of M). So C(9^n) = C(9^(n−1)) + P(n),
   where P(n) counts the primitive sorted solutions (all coordinates prime to 3).
2. So the corrected conjecture holds if and only if P(n) = (3^(n−1) + 1)/2 for all n ≥ 1.
3. Count via r_3. The Gauss–Hurwitz formula
   r_3(m²) = 6 ∏_{p^e ∥ m, p odd} (σ(p^e) − (−1/p) σ(p^(e−1))) gives
   r_3(9^n) = 6(2·3^n − 1). The equation x² + y² = 9^n has only the solutions (±3^n, 0) and
   (0, ±3^n), by the same descent. So exactly 6 integer representations have a zero coordinate.
   3a² = 9^n is impossible, and 2a² + c² = 9^n has exactly n positive solutions. That leaves
   48D + 24n = 12·3^n − 12 for the D sorted triples with distinct entries, and
   C = D + n = (3^n + 2n − 1)/4.

**Evidence.**
- [`A047926_mathlib.lean`](A047926_mathlib.lean) (Mathlib).
  - `A047926_misindexed`: C(9) = 1 ≠ a(1) = 3, C(81) = 3 = a(1), C(729) = 8 = a(2).
  - `A047926_desc`: the descent C(9M) = C(M) + #primitive.
  - `A047926_iff`: (∀ n, C(9^(n+1)) = a(n)) ↔ (∀ n, 2P(n+1) = 3^n + 1).
  - `A047926_P_small`: P(1), P(2), P(3) = 1, 2, 5.
  - Axioms: propext, Classical.choice, Quot.sound.
- Outside Lean: P(n) = (3^(n−1) + 1)/2 for n ≥ 4, which is the Gauss–Hurwitz value r_3(9^n),
  plus the orbit count in step 3. Mathlib has no r_3 formula. The binary count (n solutions of
  2a² + c² = 9^n) is elementary: there is one primitive solution per n, unique by the
  divisibility trick 9^n | (y₁x₂ − x₁y₂)(y₁x₂ + x₁y₂). It is not formalised here because the
  Lean reduction does not need it.
- `certificate/check.py` checks C(9^n) and P(n) for n ≤ 7 and r_3(9^n) for n ≤ 5.

**Review level.** lean-proof for the reduction and the misindexing. The corrected statement
itself is rechecked numerically and rests on the classical formula.

**Prior art (2026-11-05).** The OEIS entry is unchanged and states the comment as a conjecture
with the off-by-one examples. The r_3(n²) formula is classical (Hurwitz 1907; see Hirschhorn and
Sellers, "On representations of a number as a sum of three squares", for 9^λ·n), so the
corrected count is a known consequence. google-deepmind/formal-conjectures has no file for
A047926.
