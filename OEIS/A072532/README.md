# OEIS A072532: "k < a(n-1)" fails at n = 1, 2; the corrected claim is open

**Source.** [A072532](https://oeis.org/A072532) (offset 0): a(0) = 1; for n > 0, a(n) = smallest prime of the form
k·a(n-1) - 1 with k > 1 (Amarnath Murthy, 2002). Comment: "Conjecture: If a(n) = k*a(n-1)-1 then k < a(n-1)."
(OEIS text, CC BY-SA 4.0, checked 2026-11-07.)

**Result.** As written the conjecture is false: n = 1 has k = 3 > a(0) = 1, and n = 2 has k = 2 = a(1). For n ≥ 3
(the intended reading) it holds for n ≤ 160 (k ≤ 3194, a(159) has 330 digits; terms are BPSW probable primes) and
is open.

**Argument.** a(1): 2·1 - 1 = 1 is not prime, 3·1 - 1 = 2 is. a(2): 2·2 - 1 = 3 is prime.

**Reduction of the corrected claim.** For n ≥ 3, q = a(n-1) is an odd prime ≥ 3 and k = 1 gives the even number
q - 1, so the claim says: the least prime p ≡ -1 (mod q) with p > q - 1 is below q^2 - 1. It follows from the
conjecture that the least prime in every reduced class mod q is below q^2 (expected from Heath-Brown's conjecture
p(a, q) ≪ φ(q) log^2 q). Known bounds do not reach it: Linnik's theorem with exponent 5 (Xylouris 2011), and even
GRH gives only p ≤ (1 + o(1)) (φ(q) log q)^2 (Bach-Sorenson 1996), larger than q^2.

**Evidence.**
- Lean (core): [`A072532.lean`](A072532.lean): `step1`, `step2` (least k for n = 1, 2), `literal_false_n1`,
  `literal_false_n2`. Checked with `tools/leancheck.sh`; no axioms.
- [`certificate/seq.gp`](certificate/seq.gp), [`certificate/seq.out`](certificate/seq.out): n, k, digits of
  a(n-1), whether k < a(n-1), k/log^2 a(n-1), for n ≤ 160. Max of k/log^2 a(n-1) for n ≥ 3 is 1.66 (n = 3).
- Outside Lean: none for the literal failure. The n ≤ 160 check uses BPSW probable primes and is script-only.

**Review level.** `lean-witness`.

**Prior art.** Checked 2026-11-07: OEIS entry (conjecture unchanged, no restriction to n ≥ 3), formal-conjectures,
oeis-lean-proofs: nothing found.
