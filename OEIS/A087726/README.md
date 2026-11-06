# OEIS A087726: a(n) = n^2 if and only if n is squarefree

**Source.** [A087726](https://oeis.org/A087726) (offset 1), Yuval Dekel, Sep 28 2003: "Number of elements X in the
matrix ring M_2(Z_n) such that X^2 == 0 mod n." Comment: "Conjecture: a(n)=n^2 if and only if n is squarefree. [Ben
Branman, Mar 22 2013]". Further comments: the squarefree direction is true (Eric M. Schmidt, Mar 23 2013); a
conjectured prime-power formula a(p^k) = (1+3p^2+2k(p^2-1)+(-1)^k(p^2-1)) p^(2k-2)/4 "would imply the conjecture"
(Robert Israel, Jun 10 2015); a proof for k = 1 (Manfred Scheucher, linked pdf). (OEIS text, CC BY-SA 4.0, revision
#27 of Jun 11 2015, checked 2026-11-06.)

**Result.** True: for n >= 1, a(n) = n^2 iff n is squarefree. Moreover a(n) >= n^2 for all n >= 1, and
a(p^k) > p^(2k) for every prime p and k >= 2. Israel's formula is also true: for every prime p and k >= 1,
a(p^k) = p^(4 floor(k/2)) + ceil(k/2) p^(2k-2) (p^2 - 1) = (1+3p^2+2k(p^2-1)+(-1)^k(p^2-1)) p^(2k-2)/4.

**Argument.**
1. *Multiplicative.* For coprime m, n the ring isomorphism Z/mn = Z/m x Z/n, applied entrywise, maps square-zero
   matrices bijectively onto pairs of square-zero matrices.
2. *Primes.* Over the field F_p, X^2 = 0 forces det X = 0 and then tr(X) X = 0, so X = [[a, b], [c, -a]] with
   a^2 + bc = 0. If b != 0, c = -a^2/b (p(p-1) matrices); if b = 0 then a = 0 and c is free (p matrices, including 0).
   So a(p) = p^2.
3. *Prime powers, k >= 2.* In Z/p^k three disjoint families of square-zero matrices:
   - [[a, u], [-a^2/u, -a]] with u a unit: p^k phi(p^k) matrices (entry (0,1) a unit);
   - [[pt, -(pt)^2/u], [u, -pt]] with u a unit, 0 <= t < p^(k-1): p^(k-1) phi(p^k) (entry (1,0) a unit, entry (0,1)
     a multiple of p);
   - matrices with entries (0,0), (1,0), (1,1) multiples of p^h, h = ceil(k/2), and entry (0,1) a multiple of
     p^l, l = floor(k/2) >= 1: every entry of X^2 is a multiple of p^(2h) or p^(h+l) = p^k, so X^2 = 0;
     p^(3l+h) matrices (entries (0,1), (1,0) non-units).
   For even k the third family alone has p^(2k) elements; for odd k = 2m+1 the sum is
   p^(4m)(p(p-1) + (p-1) + p) = p^(4m)(p^2 + p - 1) > p^(2k). Either way a(p^k) > p^(2k).
4. By 1-3 and induction over the factorisation, a(n) = prod a(p^k) >= prod p^(2k) = n^2, with equality iff every
   exponent is 1.

5. *Exact count (Israel's formula).* Split the square-zero X mod p^(m+2) by whether some entry is a unit.
   - Primitive X: X^2 = tr(X) X - det(X) I and X mod p is a non-scalar nilpotent, so tr X = det X = 0. If the
     (0,1) entry is a unit, X is in the first family of step 3; if not, the (1,0) entry is a unit (otherwise
     a^2 = -bc and d^2 = -bc are non-units, so no entry is a unit), and a^2 = -bc forces p | a: the second family.
     Count p^(m+2) phi + p^(m+1) phi = p^(2m+2)(p^2 - 1).
   - Non-primitive X: every entry is p w + p^(m+1) t with w mod p^m and 0 <= t < p, uniquely. Then
     X^2 = p^2 W^2 mod p^(m+2), so X^2 = 0 iff W^2 = 0 mod p^m: p^4 a(p^m) matrices.
   So a(p^(m+2)) = p^(2m+2)(p^2-1) + p^4 a(p^m), with a(1) = 1 and a(p) = p^2. Induction gives
   a(p^k) = p^(4 floor(k/2)) + ceil(k/2) p^(2k-2)(p^2-1), which equals Israel's expression for both parities.

**Evidence.**
- Lean (Mathlib): [`A087726_mathlib.lean`](A087726_mathlib.lean). Definition: `A087726 n = Nat.card {X : Matrix
  (Fin 2) (Fin 2) (ZMod n) // X * X = 0}`. Main theorem `OEIS087726.A087726_conj : 1 ≤ n → (A087726 n = n ^ 2 ↔
  Squarefree n)`. Also `A087726_ge`, `A087726_mul` (step 1), `A087726_prime` (step 2), `A087726_prime_pow_gt`
  (step 3, families `fb`, `fc`, `fg`), `A087726_main` (step 4, `Nat.recOnPosPrimePosCoprime`). Israel's
  formula: `OEIS087726.A087726_israel : 1 ≤ k → 4 * (A087726 (p ^ k) : ℤ) = (1 + 3p^2 + 2k(p^2-1) + (-1)^k(p^2-1))
  * p^(2k-2)` for every prime p, via `prim_sq_mem`, `psi`, `psi_surj`, `Psi_inj`, `Psi_sq_iff`, `A087726_rec`,
  `A087726_prime_pow_closed` (step 5). Check:
  `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext, Classical.choice, Quot.sound. No
  `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py) with the entry's b-file
  ([`certificate/b087726.txt`](certificate/b087726.txt), n <= 1000, Manfred Scheucher): brute force matches for
  n <= 30; the conjecture and a(n) >= n^2 hold for n <= 1000; the three-family count lies strictly between p^(2k)
  and a(p^k) for prime powers up to 1000; Israel's formula and the recursion of step 5 match all prime powers up to
  1000.
- Outside Lean: none. Not verified in Lean: agreement with the OEIS data (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry (last edited 2015) records the squarefree direction as proved (Schmidt;
it is a(p) = p^2 plus multiplicativity, Scheucher's pdf proves a(p) = p^2) and leaves the converse depending on
Israel's unproved prime-power formula. No later proof found: not in google-deepmind/formal-conjectures (no
`FormalConjectures/OEIS/87726.lean`) or otoi-lab/oeis-lean-proofs; web search found none; arXiv:2209.03626 counts
solutions of P(X) = 0 in M_n(Z/p^k) only for P squarefree mod p, which excludes X^2. The converse direction
(the lower bound a(p^k) > p^(2k)), the proof of Israel's formula and the Lean proofs are new as far as found.
