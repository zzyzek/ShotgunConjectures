# Guy A19 (Erdős): infinitely many n with every n − 2^k squarefree

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section A19
(values of n making n − 2^k prime). Alongside the prime question, Guy records Erdős's conjecture
that there are infinitely many n for which n − 2^k is squarefree for every k with 2^k < n.
OEIS [A091155](https://oeis.org/A091155) lists these n and says "Erdős conjectures that this
sequence is infinite". Original reference: P. Erdős, On integers of the form 2^k + p and some
related problems, *Summa Brasil. Math.* 2 (1950), 113–123.

**Reading.** k runs over all k ≥ 0 with 2^k < n (k = 0 included, so n − 1 must be squarefree).
n = 1 satisfies the condition vacuously; OEIS starts at 2. Neither affects infinitude.

**Result.** Proved: the set {n : n − 2^k is squarefree for every k ≥ 0 with 2^k < n} is
infinite. Quantitatively, for every s ≥ 20 there is such an n with s < n ≤ 2^(9702 s).

**Argument.** Fix s ≥ 20 and put y = 2310 s, L = 4851 s, K = 2L, x = 2^K. Let R be the product
of the odd primes ≤ y and M = 4R. Choose c < M with c ≡ 3 (mod 4) and R ∣ c (c = 3R if
R ≡ 1 mod 4, else c = R). The candidates are n_j = c + Mj for 0 ≤ j < J = ⌊x/M⌋ − 1; all are
≤ x, so for a candidate n the relevant k satisfy k < K.

1. *p = 2.* n ≡ 3 (mod 4), so n − 1 ≡ 2, n − 2 ≡ 1 and n − 2^k ≡ 3 (mod 4) for k ≥ 2. Hence
   4 ∤ n − 2^k.
2. *Odd p ≤ y.* p ∣ R ∣ n and p ∤ 2^k, so p ∤ n − 2^k.
3. *p > y.* If p² ∣ n − 2^k then p² < x, so p ≤ 2^L. For fixed (k, p) the candidates with
   p² ∣ n − 2^k are congruent to each other mod M (all ≡ c) and mod p² (all ≡ 2^k), and
   gcd(M, p²) = 1, so they are congruent mod Mp². Numbers ≤ x in one class mod Mp² number at
   most x/(Mp²) + 1.
4. *Prime sum.* A prime p > y ≥ 11 is coprime to 2310. Split m > 2310 s with gcd(m, 2310) = 1
   into blocks [2310 j, 2310 j + 2310), j ≥ s; each block holds φ(2310) = 480 such m, each with
   1/m² ≤ 1/(2310 j)². With 1/j² ≤ 1/(j−1) − 1/j (telescoping),
   Σ_{p prime, p > y} 1/p² ≤ (480/2310²) Σ_{j ≥ s} 1/j² ≤ 480/(2310² (s − 1)) =: σ.
   Then Kσ = 9702 s · 480 / (2310² (s − 1)) ≤ 23/25 for s ≥ 20 (it equals 0.9187 at s = 20 and
   decreases to 0.8727).
5. *Count.* Suppose no candidate is good. Each candidate lies in some set of step 3, so with
   a = x/M,
   a − 2 ≤ J ≤ Σ_{k<K} Σ_{y<p≤2^L} (x/(Mp²) + 1) ≤ K(aσ + 2^L) ≤ (23/25) a + K 2^L.
   So 2a ≤ 25 (K 2^L + 2). But R ≤ primorial(y) ≤ 4^y gives M ≤ 2^(2y+2) and
   a ≥ 2^(K − 2y − 2) = 2^(5082 s − 2) = 2^L · 2^(231 s − 2), while
   25 (K 2^L + 2) ≤ 242600 s · 2^L < 2^18 · 2^s · 2^L ≤ 2 · 2^L · 2^(231 s − 2). Contradiction.
6. So some candidate n is good. By Bertrand there is a prime q with 1155 s < q ≤ 2310 s = y;
   q is odd, so q ∣ R and n ≥ c ≥ R ≥ q > s. As s is arbitrary, there are infinitely many good n.

The only arithmetic input beyond counting is the primorial bound n# ≤ 4^n and Bertrand's
postulate. The block bound replaces a prime-counting estimate: the union bound needs
K Σ_{p>y} 1/p² < 1 while the modulus M must stay below about √x, and the crude bound
Σ_{m>y} 1/m² ≤ 1/y does not fit both with M ≤ 4^y; restricting m to residues coprime to 2310
(density 480/2310 ≈ 0.208) does, with K/y = 4.2 in the window (4, 4.81).

**Evidence.**
- Lean + Mathlib: [`A19_2_mathlib.lean`](A19_2_mathlib.lean).
  `A19_2_main : Set.Infinite {n : ℕ | ∀ k : ℕ, 2 ^ k < n → Squarefree (n - 2 ^ k)}`, from
  `A19_exists (s : ℕ) (hs : 20 ≤ s) : ∃ n, s < n ∧ ∀ k : ℕ, 2 ^ k < n → Squarefree (n - 2 ^ k)`.
  Parts: `A19_card_le_of_modEq` (step 3 count), `A19_tele`, `A19_totient_2310`,
  `A19_sum_coprime` (step 4), `A19_R_le`/`A19_dvd_R`/`A19_coprime_R`/`A19_R_odd` (odd primorial),
  `A19_final` (step 5 arithmetic). Mathlib inputs: `primorial_le_four_pow`,
  `Nat.filter_coprime_Ico_eq_totient`, `Nat.exists_prime_lt_and_le_two_mul` (Bertrand),
  `Nat.squarefree_iff_prime_squarefree`. Axioms: propext, Classical.choice, Quot.sound. No
  `native_decide`. Checked with `tools/leancheck-mathlib.sh` (exit 0, no warnings).
  Outside Lean: nothing for the theorem. The A091155 term list below is checked in Python only;
  the Lean file does not mention it.
- `certificate/terms.py` (output `terms.out`): recomputes A091155 to 10⁶; matches all 53
  published terms; 6965 terms ≤ 10⁶ (counting n = 1); the only terms not ≡ 3 (mod 12) are
  1, 2, 4, 7, 23, as OEIS notes.
- `certificate/constants.py` (output `constants.out`): φ(2310) = 480; Kσ ≤ 23/25 exactly for
  s = 20, 21, 100, 10⁶; log₂ of both sides of the step-5 inequality at s = 20 (97042 vs 101639);
  the block bound against the actual coprime and prime sums for y = 2310 s, s = 2, 5, 20, 100;
  and K Σ_{p>z} 1/p² ≈ 0.39–0.47 for the original sketch (z = 3 ln x / ln ln x), confirming the
  sketch's union bound with true prime sums.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05.
- erdosproblems.com [#1142](https://www.erdosproblems.com/1142) is the *prime* version (open;
  only 4, 7, 15, 21, 45, 75, 105 known). Its page does not state the squarefree variant; the
  forum thread has one comment (2026-02-09) saying a positive answer is expected for the
  squarefree version, with no proof. No separate erdosproblems entry for the squarefree variant
  was found.
- teorth/erdosproblems wiki "AI contributions to Erdős problems": no entry for 1142, no mention of
  A091155 or the squarefree variant.
- OEIS A091155: conjecture stated, no proof cited.
- google-deepmind/formal-conjectures `FormalConjectures/ErdosProblems/1142.lean`: formalises
  only the prime version, `erdos_1142` tagged `research open` (plus the Mientka–Weitzenkamp
  computation tagged `research solved`, with `sorry`). No squarefree variant, no formal proof.
- Web search (squarefree n − 2^k, infinitely many): nothing beyond the conjecture; the nearby
  results concern odd numbers as squarefree + 2^k (arXiv 2411.01964) and #1209.
- Guy, UPINT 3rd ed. (2004), A19: states the squarefree version as Erdős's conjecture, no proof.
- Erdős, Summa Brasil. Math. 2 (1950) 113-123 (cited by A091155): read pages 1-5, 7-9, 11-12 of the scan; it treats the prime version (n = 105) and 2^k + p, not the squarefree version.
No proof found. The argument is an elementary sieve; it would fit as an OEIS comment on A091155
and an erdosproblems forum note on #1142.
