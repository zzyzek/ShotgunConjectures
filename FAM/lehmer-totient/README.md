# Lehmer's totient problem (FAM-lehmer-totient) and the cube-count core (OEIS-A123365)

Famous-problem pilot, problem 1 of 6. Date 2026-11-05. The famous problem is not settled.

## Statements

* **Lehmer (1932).** Is there a composite n > 1 with φ(n) | n − 1? Call such n a *Lehmer number*
  (Lean `IsLehmer n := 1 < n ∧ ¬ n.Prime ∧ n.totient ∣ n - 1`, the same statement as
  formal-conjectures `LehmerTotient.lehmer_totient`). Open.
* **Core core-multiplicative-exact-target, step for A123365.** c(n) = number of cubes mod n.
  OEIS A123365 conjectures that 3c(n) = n + 2 holds only for n = 1 and the primes p ≡ 1 (mod 6).

## Results

### A. Lehmer numbers (all in Lean, `lehmer_totient_mathlib.lean`)

| Lean name | Statement |
|---|---|
| `squarefree_of_isLehmer` | a Lehmer number is squarefree |
| `odd_of_isLehmer` | a Lehmer number is odd |
| `isCarmichael_of_isLehmer` | a Lehmer number is a Carmichael number (Mathlib's `Nat.IsCarmichael`) |
| `three_le_card_of_isLehmer` | at least 3 distinct prime factors (Mathlib, via Carmichael) |
| `prime_lt_of_isLehmer` | for each prime factor p: p < k(A + 1), A = product of the prime factors below p, k = number of prime factors at least p |
| `le_bound_of_isLehmer` | with K distinct prime factors, n ≤ (2K)^(2^K − 1) |
| `finite_isLehmer_card` | for each K, the Lehmer numbers with exactly K distinct prime factors form a finite set |
| `four_le_card_of_isLehmer` | at least 4 distinct prime factors |

Axioms (from `tools/leancheck-mathlib.sh`): propext, Classical.choice, Quot.sound only
(`check3_eq` uses none). No sorry, no native_decide, zero warnings.

### B. Cube counts (`OEIS/A123365/A123365_mathlib.lean`)

| Lean name | Statement | Hypotheses |
|---|---|---|
| `cq_equation_no_solution` | for primes p ≡ 1, q ≡ 2 (mod 3) and e ≥ 1: (p + 2)·cq(q, e) ≠ p·q^e + 2 | none (cq is the closed form, see below) |
| `three_c_eq_one_factor` | 3c(x^a) = x^a + 2 with x prime, a ≥ 1 forces a = 1 and x ≡ 1 (mod 3) | closed forms |
| `three_c_ne_of_two_factors` | for distinct primes x, y and a, b ≥ 1: 3c(x^a y^b) ≠ x^a y^b + 2 | closed forms |

"Closed forms" = three hypotheses on the function c, stated in the file:
c(mk) = c(m)c(k) for coprime m, k; c(q^e) = 1 + (q − 1)·s1(q, e) for primes q ≡ 2 (mod 3);
3c(p^e) = 3 + (p − 1)·s1(p, e) for primes p ≡ 1 (mod 3); where s1(q, e) is the sum of q^(j−1)
over 1 ≤ j ≤ e, j ≡ e (mod 3). These are **not proved in Lean**. They are checked by brute force
(certificate/cube_checks.py`: q ∈ {2, 5, 11, 17, 23}, p ∈ {7, 13, 19, 31}, prime powers up to 60000;
also `work/tier2/A123365/probe.py`). The Lean definition of c as a cube count in `ZMod n` is not
connected to the hypotheses. Same axioms line as A.

**K covered.** For the equation 3c(n) = n + 2: every n with at most 2 distinct prime factors is
classified (on paper, and in Lean modulo the closed forms): the solutions are n = 1 and the primes
p ≡ 1 (mod 6). For the second equation (p + 2)c(B) = pB + 2 with p prime ≡ 1 (mod 6): no solution
with B a prime power q^e, q ≡ 2 (mod 3). Nothing is proved for 3 or more prime factors beyond the
partial reductions listed under Obstacles.

## Arguments

### A. Lehmer

1. *Squarefree.* If p² | n then p | p(p − 1) = φ(p²) | φ(n) | n − 1 and p | n, so p | 1.
2. *Odd.* n > 2 (n = 2 is prime), so φ(n) is even, so 2 | n − 1.
3. *Carmichael.* For p | n: p − 1 = φ(p) | φ(n) | n − 1. With 1 this is Korselt's criterion
   (Mathlib `Nat.isCarmichael_iff_korselt`); Mathlib then gives 3 or more prime factors.
4. *Gap.* Write n − 1 = mφ(n). m = 0 gives n = 1, m = 1 gives φ(n) = n − 1, so n prime. Hence m ≥ 2.
5. *Prime bound (Pomerance 1977, Lemma 3, a = 1).* Fix a prime factor p. Split n = A·B with A the
   product of the prime factors below p and B the rest (k primes, all ≥ p); let Φa = φ(A),
   Φb = φ(B). If mΦa ≤ A then n − 1 = mΦaΦb ≤ A(B − 1) = n − A, so A = 1, Φa = 1, m ≤ 1, a
   contradiction. Hence mΦa ≥ A + 1 and AB − 1 = mΦaΦb ≥ (A + 1)Φb. Termwise
   (q − 1)p ≥ q(p − 1) for q ≥ p gives Φb·p^k ≥ B·(p − 1)^k, so (A + 1)(p − 1)^k < A·p^k.
   The Bernoulli-type inequality (x + 1)^k (x + 1 − k) ≤ x^k (x + 1) (x = p − 1, induction on k)
   shows that p ≥ k(A + 1) would give A·p^k ≤ (A + 1)(p − 1)^k. So p < k(A + 1).
6. *Explicit bound.* With k ≤ K and A ≥ 1, p < 2K·A. By induction on j, the product of the j
   smallest prime factors is at most (2K)^(2^j − 1); for j = K this bounds n. (Pomerance's
   sharper n < K^(2^K) needs his Theorem 2, p(n) ≤ K − 1, which uses results of Norton and Grün;
   not formalised.)
7. *Four prime factors.* If n = xyz with x < y < z, step 5 gives x < 6, y < 2(x + 1),
   z < xy + 1, and x ≥ 3 (odd). A kernel `decide` over x < 6, y < 12, z < 56 (with x ∤ z) finds
   no (x − 1)(y − 1)(z − 1) | xyz − 1.

### B. Cube counts

Notation: G(q, e) = 1 + q + … + q^(e−1), so q^e = 1 + (q − 1)G and, with the closed form,
c(q^e) = 1 + (q − 1)s1(q, e) for q ≡ 2 (mod 3).

*Prime-power equation.* (p + 2)c(q^e) = p q^e + 2 is equivalent to (p + 2)·s1 = p·G
(subtract and divide by q − 1). G ≡ 1 (mod q). s1 ≡ s1(q, e mod 3) (mod q), that is 0, 1, q for
e ≡ 0, 1, 2.
* e ≡ 0, 2 (mod 3): q | s1, so q | pG, so q | p, so q = p, impossible since p ≡ 1, q ≡ 2 (mod 3).
* e ≡ 1 (mod 3): s1 ≡ 1, so p + 2 ≡ p (mod q), so q = 2. Write e = 3t + 1, u = 8^t. Then
  7s1 + 1 = 8u and G = 2u − 1, and the equation becomes (u − 1)(3p − 8) = 7. t = 0 gives 0 = 7;
  t ≥ 1 gives u − 1 ≥ 7 and 3p − 8 ≥ 4 (p ≥ 4), product ≥ 28.
For any prime p the only solution is p = 3, B = 16 (t = 1, 3p − 8 = 1); the search in
certificate/cube_checks.py` (q < 2000, e ≤ 12) finds exactly this one.

*Two prime factors x^a y^b with 3c(n) = n + 2.* n ≡ 1 (mod 3), so neither prime is 3.
* Both ≡ 1 (mod 3): 3c(X) ≤ X + 2 for X = x^a (equality at a = 1), so 9c(X)c(Y) ≤ (X + 2)(Y + 2)
  < 3(XY + 2) since (X − 1)(Y − 1) > 0.
* x ≡ 1, y ≡ 2 with a ≥ 2: 3c(X) + 2 ≤ X (because G − s1 ≥ 1 for a ≥ 2 and x − 1 ≥ 6) and
  c(Y) ≤ Y, so 3c(n) < n. With a = 1: 3c(x) = x + 2 and the equation is the prime-power equation.
* Both ≡ 2 (mod 3): x·c(X) > (x − 1)X and y·c(Y) > (y − 1)Y, and 3(x − 1)(y − 1) ≥ xy + 2 for
  distinct primes x, y ≡ 2 (mod 3) (smallest pair 2, 5), so 3xy·c(n) > (xy + 2)XY ≥ xy(XY + 2).
*One prime factor:* x ≡ 2 gives 3c(X) > X + 2 (x = 2, a = 1 by hand), x ≡ 1 needs a = 1.

## Obstacles (why nothing more falls)

* **Lehmer, all K.** The prime-bound argument bounds each prime by the product of the smaller
  ones, so it gives finiteness for each K and nothing uniform in K. This is the same barrier as
  in the literature (best known: ω(n) ≥ 14 or 15, density O(x^{1/2}(log x)^{3/4})). Pushing
  `four_le_card` to 5 by the same `decide` route needs ~18000 triples (x < 8, y < 24,
  z < 2(xy + 1)) with the last prime determined by the exact equation; not attempted (time box;
  Lehmer's ω ≥ 7 is classical).
* **Cube counts, 3 or more prime factors.** After the local bounds, the open cases are
  (A) n = pB, B built from primes ≡ 2 (mod 3), ω(B) ≥ 2; and (B) all primes ≡ 2 (mod 3).
  Case B with ω(n) ≤ 4 is excluded on paper by the ratio bound c(q^e)/q^e > 1 − 1/q
  (product over the four smallest such primes 2, 5, 11, 17 is 0.342 > 1/3); not in Lean.
  The Lehmer-type gap argument does not transfer:
  (i) the prime p ≡ 1 (mod 3) has local ratio c(p)/p ≈ 1/3, not near 1, so it sets the target
  p/(p + 2) for c(B)/B itself; the gap bounds the smallest prime of B by about k(p + 1), while
  p = 2(c(B) − 1)/(B − c(B)) is about twice the smallest prime of B, so there is no absolute bound;
  (ii) exponents are unbounded: c(q^e)/q^e does not tend to 1 but oscillates with e mod 3 between
  three limits, so bounding the primes does not bound n. The mod-q argument that closes
  ω(B) = 1 (c(q^e) ≡ 0 or 1 mod q by e mod 3) gives for ω(B) = 2 only congruences: odd q need
  exponent ≢ 1 (mod 3), and (p + 2)c(r^b) ≡ 2 (mod q). No contradiction.

## Evidence

* `lehmer_totient_mathlib.lean`, `OEIS/A123365/A123365_mathlib.lean` (checked 2026-11-05 with
  `tools/leancheck-mathlib.sh`, Lean 4.35.0, Mathlib 56a00585).
* certificate/lehmer_checks.py`: the K = 3 finite search (no solutions; without the x ∤ z filter
  the only hit is (3, 5, 15)), and no composite n < 10^6 with φ(n) | n − 1.
* certificate/cube_checks.py`: closed forms vs brute force; prime-power equation search; 3c(n) = n + 2
  for n < 20000 by brute force gives only 1 and primes ≡ 1 (mod 6).
* Outside Lean: the closed forms for c at prime powers and the multiplicativity of c (B);
  Pomerance's sharper K^(2^K); the case-B ω ≤ 4 ratio bound; all literature bounds.

## Prior art (checked 2026-11-05)

* formal-conjectures `FormalConjectures/Wikipedia/LehmerTotient.lean` (raw file fetched):
  one statement, `@[category research open]`, proof `sorry`, no `formal_proof` link, no solved
  variants.
* Mathlib (rev 56a00585): no Lehmer totient material; Carmichael numbers are there
  (`NumberTheory/CarmichaelNumber.lean`: odd, squarefree, Korselt, ≥ 3 prime factors), so the
  squarefree/odd/≥ 3 statements are Mathlib facts once `isCarmichael_of_isLehmer` (new, short)
  is proved. New here in Lean: the link to Carmichael, Pomerance's Lemma 3 (a = 1), the
  explicit fixed-K bound and finiteness, ω ≥ 4.
* OpenAI math repo (`~/claude/openai-math/repo`, lean/OAI and CONTENTS.md): no Lehmer totient
  content (only a Lucas–Lehmer certificate and unrelated totient papers).
* Web search (Lean formalisations of Lehmer's totient problem): nothing found.
* Literature. Pomerance, *On composite n for which φ(n) | n − 1, II*, Pacific J. Math. 69 (1977)
  177–186 (read: Lemma 3 is the prime bound above; Theorem 3 gives n < K^(2^K); the
  introduction cites Lieuwens ω ≥ 11 and Kishore ω ≥ 13). Recalled, not re-checked: Lehmer,
  Bull. AMS 38 (1932) (ω ≥ 7); Cohen and Hagis 1980 (ω ≥ 14); later bounds ω ≥ 15 and n > 10^30.
* A123365: no proof found earlier (see methods/attempts.jsonl); the K ≤ 2 classification here is
  not claimed anywhere we found. The prime-power equation result is elementary.
