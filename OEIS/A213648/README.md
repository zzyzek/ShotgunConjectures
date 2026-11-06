# OEIS A213648: fixed points lie in A000057

**Source.** [A213648](https://oeis.org/A213648) (offset 2): "The minimum number of 1's in the relation
n*[n,1,1,...,1,n] = [x,...,x] between simple continued fractions." Comment: "Conjecture: the fixed points of this
sequence are in A000057." [A000057](https://oeis.org/A000057): primes dividing at least one term of every
Fibonacci-type sequence, equivalently primes p whose Fibonacci entry point z(p) (A001177) is p + 1. (OEIS text,
A213648 revision #68 of Aug 18 2026, checked 2026-11-06.)

**Result.** True, and settled in the entry itself: M. Jeremie Lafitte (Levitas), Aug 10 2026, added a formula
section proving a(n) = A001177(n) - 1 = min{m ≥ 1 : n | F(m+1)} (the symmetric continuant matrix
M(n) M(1)^m M(n) = [[P, Q], [Q, F(m+1)]] and the Euclidean algorithm), so the fixed points are the n with
z(n) = n + 1. A001177 states "a(n) = n + 1 if and only if n is in A000057" (Benoit Cloitre, 2007) without proof;
we supply the step that z(n) = n + 1 forces n prime.

**Argument (z(n) = n + 1 implies n prime).** Write z(m) for the entry point; m | F(k) iff z(m) | k.
1. For p^e ∥ n, z(p^e) | z(n) = n + 1, which is coprime to p, so p ∤ z(p^e). Since 5 | z(5^e) = 5^e, 5 ∤ n.
2. Let a = z(p). F(at) ≡ t F(a) F(a+1)^(t-1) (mod F(a)^2) and p ∤ F(a+1), so v_p(F(at)) = v_p(F(a)) when p ∤ t.
   With t = z(p^e)/a this gives p^e | F(a), so z(p^e) = z(p), which divides p - (5/p) (for p = 2: z(2) = 3, and
   z(4) = 6 is even, so 4 ∤ n).
3. Hence n + 1 divides L = lcm over p | n of (p - (5/p)). If n = p^e then p^e + 1 ≤ p + 1, so e = 1. If n has
   r ≥ 2 odd prime factors and is odd, L ≤ 2 Π (p+1)/2 ≤ 2 (2/3)^r Π p < n + 1. If n = 2m (m odd, m > 1), n + 1 is
   odd and divides the odd part of L, which is at most 3 Π_{p | m} (p+1)/2 < 2m + 1. Contradiction in both cases.

**Evidence.**
- [`certificate/check.py`](certificate/check.py): a(n) from the continued-fraction definition for n ≤ 400 and
  z(n) - 1 for n ≤ 10000 both equal the b-file; the fixed points up to 10000 are exactly the 249 terms of A000057
  up to 10000; no composite n ≤ 2·10^5 has z(n) = n + 1.
- Lean (Mathlib): [`A213648_mathlib.lean`](A213648_mathlib.lean). `EP_prime : 2 ≤ n → n ∣ F(n+1) → (∀ m, 1 ≤ m →
  m ≤ n → ¬ n ∣ F(m)) → n.Prime` (steps 1-3: `kam` gives p ∣ F(p−1)F(p)F(p+1) from (A^p)^2 = A^p + 1 for the
  Fibonacci matrix over ZMod p; `lift` is the Fibonacci lifting lemma; `per_prime`, `claim`, `comb`, `ineq` give the
  lcm bound, with the case 4 ∣ n and n = 2m handled separately). Check: `tools/leancheck-mathlib.sh`, exit 0, no
  warnings; axioms at most propext, Classical.choice, Quot.sound. Outside Lean: Lafitte's continued-fraction lemma
  a(n) = A001177(n) − 1 (as published in the entry).

**Review level.** `rechecked`.

**Prior art** (2026-11-06). Settled in OEIS A213648 (Lafitte, Aug 10 2026; the conjecture line is answered by a
comment "The conjecture above is true"); A001177 formula line (Cloitre) for z(n) = n + 1; A000057 comments
(Hasler 2015, Lafitte 2026). google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs: no file.
