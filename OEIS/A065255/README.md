# OEIS A065255: b(k)/k → 10

**Source.** [A065255](https://oeis.org/A065255) (B. Cloitre, Aug 06 2002): "Consider the sequence b(k) such that
b(k) and sigma(b(k)) end with the same digit in base 10. Sequence gives values of b(k) such that b(k)/k = 10."
Comment: "Conjecture: lim n -> infinity b(k)/k = 10." OEIS text, CC BY-SA 4.0, checked 2026-11-07.

**Reading.** b is the increasing enumeration of B = {n >= 1 : sigma(n) ≡ n (mod 10)} (1, 14, 34, 40, ...).
The conjecture is b(k)/k → 10, i.e. B has natural density 1/10.

**Result.** True. B differs from the multiples of 10 by a set of density 0, so B has density 1/10 and
b(k) ~ 10k.

**Argument.**
1. *Key lemma.* If a prime p ≡ 9 (mod 10) divides n exactly once, then 10 | sigma(n): write n = p m with
   p ∤ m; sigma is multiplicative, so sigma(n) = (p + 1) sigma(m) and 10 | p + 1. Then sigma(n) ≡ n (mod 10)
   iff n ≡ 0 (mod 10).
2. *Almost every n has such a prime.* Let P be the primes ≡ 9 (mod 10) and E the set of n such that no
   p in P divides n exactly once. Every n in E is n = s m with s P-squarefull (each prime of s lies in P and
   divides s at least twice) and m free of primes in P. By Dirichlet's theorem in the quantitative form
   (Mertens for progressions), the sum of 1/p over p in P diverges, so prod_{p in P, p <= z} (1 - 1/p) → 0.
   Given eps > 0 fix z with that product < eps; inclusion-exclusion over the finitely many p in P below z
   gives #{m <= y : m free of P} <= eps y + 2^{pi(z)}. Summing over s,
   #E(x) <= sum_{s <= x, s P-squarefull} (eps x/s + 2^{pi(z)}) <= eps x C + 2^{pi(z)} #{squarefull s <= x},
   with C = sum of 1/s over squarefull s (finite) and #{squarefull s <= x} = O(sqrt x). So
   limsup #E(x)/x <= C eps for every eps, i.e. E has density 0.
3. *Conclusion.* B and 10N agree outside E, so |#B(x) - x/10| <= #E(x) + 1 = o(x). Hence B has density 1/10
   and b(k)/k → 10.

**Evidence.**
- Lean (Mathlib + `OpenProblemsLib.PNTApps`): [`A065255_mathlib.lean`](A065255_mathlib.lean), the whole argument.
  `A065255_ten_dvd_sigma`, `A065255_iff` (step 1); `A065255_exceptional_density_zero` (step 2, via
  `density_zero_of_sieve` with G_p(n) = "p divides n exactly once" and Dirichlet's divergence
  `not_summable_one_div_prime_mod` for p ≡ 9 mod 10; the sieve over finitely many p ≡ 9 mod 10 replaces the
  squarefull decomposition); `A065255_density` (B has density 1/10); `A065255_main`
  (`Nat.nth B k / (k + 1) → 10`, i.e. b(k)/k → 10 for the 1-indexed b). Checked 2026-11-08 with
  `tools/leancheck-mathlib.sh`: OK, axioms propext, Classical.choice, Quot.sound. Library guide:
  [lib/docs/pnt-applications.md](../../lib/docs/pnt-applications.md).
- [`certificate/count.py`](certificate/count.py), output [`certificate/count.out`](certificate/count.out):
  x/#B(x) = 10.06, 10.001, 9.978, 9.979 at x = 10^4, 10^5, 10^6, 3·10^6. The proportion of n <= x with
  10 ∤ sigma(n) falls slowly (0.66, 0.62, 0.59, 0.58), as expected from a (log x)^(-c) rate.
- Outside Lean: none.

**Review level.** `lean-proof` (the conjecture as stated, b(k)/k → 10, proved in Lean).

**Prior art.** Checked 2026-11-07: the OEIS entry (conjecture still stated), google-deepmind/formal-conjectures
and otoi-lab/oeis-lean-proofs local clones (no entry). That sigma(n) is divisible by any fixed m for almost all
n is classical (the same argument with primes p ≡ -1 mod m); the consequence for A065255 is immediate but
not recorded on the entry.
