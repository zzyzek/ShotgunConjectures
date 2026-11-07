# OEIS A219196: a(15) = a(16) = 131070 and a(17..32) = 8589934590

**Source.** OEIS [A219196](https://oeis.org/A219196), a(n) = A027642(A131577(n)), the denominator of the
Bernoulli number B_{2^(n−1)} (B₀ for n = 0). Comment: "Conjecture: a(15) = a(16) = 131070, a(17) through
a(32) = 8589934590." (OEIS text, CC BY-SA 4.0.)

**Result.** True, and answered in the entry: Robert Israel (Sep 21 2015) notes that by von Staudt–Clausen
a(n) is 2 times the product of the Fermat primes ≤ 2^(n−1) + 1, so a(n) = 8589934590 for 17 ≤ n ≤ 2^33.

**Argument.** For k ≥ 1, den B_{2k} = ∏ p over primes p with p − 1 | 2k (von Staudt–Clausen). For
2k = 2^m, p − 1 | 2^m means p = 2^j + 1 with j ≤ m. For j ≤ 31 the primes 2^j + 1 are 2, 3, 5, 17, 257,
65537 (j = 0, 1, 2, 4, 8, 16). So a(15), a(16) (m = 14, 15) = 2·3·5·17·257 = 131070 and a(17..32)
(m = 16..31) = 131070·65537 = 8589934590.

**Evidence.**
- Lean (Mathlib): [`A219196_mathlib.lean`](A219196_mathlib.lean). `A219196 n = (bernoulli (A131577 n)).den`.
  `A219196_15`, `A219196_16`, `A219196_17_32`. Reusable: `bernoulli_den_eq_prod` (den B_{2k} equals the product
  of the von Staudt–Clausen primes, from Mathlib `Bernoulli.vonStaudt_clausen` and `Bernoulli.dvd_den_bernoulli`),
  `fermat_like` (primes with p − 1 | 2^m, m ≤ 31). Axioms propext, Classical.choice, Quot.sound; zero warnings.
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: settled in the entry (Israel 2015; Plouffe's empirical check to a(4215)).
Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
