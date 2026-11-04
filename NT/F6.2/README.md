# Guy F6: Q(1,6,7) = ∞ and the other four-residue subpatterns of (1,6,7,10)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section F6. Q(a,b,c) is the least R such that, for all sufficiently large
primes p, some r ≤ R has r, r + a, r + b, r + c all quadratic residues mod p (∞ if there is no
such R). Guy notes that although Q(1,6), Q(1,7), Q(5,6), Q(6,7) are finite, "it appears" that
Q(1,6,7) = ∞, and that all five four-element subpatterns of r + (0,1,6,7,10) seem to give ∞:
Q(1,6,7), Q(1,6,10), Q(1,7,10), Q(5,6,9), Q(6,7,10).

**Result.** All five are ∞.

**Argument.** Let f: ℕ → {±1} be completely multiplicative. By quadratic reciprocity and
Dirichlet's theorem, for every X there are infinitely many primes p with (ℓ/p) = f(ℓ) for all
primes ℓ ≤ X, hence (n/p) = f(n) for all n ≤ X. So Q(pattern) = ∞ as soon as some f has, for
every r ≥ 1, an element of r + pattern with f = −1.
- (0,1,6,7) and (0,1,7,10): f(n) = χ₋₄(odd part of n). For odd r, r and r + 6 (resp. r + 10)
  are odd and differ by 2 mod 4, so one is ≡ 3 (mod 4) and has f = −1; for even r use r + 1
  and r + 7.
- (0,1,6,10): Legendre symbol mod 11 (or 19); (0,5,6,9): mod 11 (or 17, 31); (0,6,7,10):
  mod 19; with any value at q itself. In each case every translate t + pattern mod q contains a
  nonzero non-residue class, so some element has f = −1. (This also works for (0,1,6,7) with
  q = 11, 17; (0,1,7,10) has no prime-modulus obstruction for q ≤ 31 and needs χ₋₄.)

**Evidence.**
- Lean (Mathlib): [`F6_2_mathlib.lean`](F6_2_mathlib.lean) proves `F6_2_main`: for each of the five patterns and all R, N there is a prime p > N such that for every r ≤ R some element of r + pattern is not a square mod p (Mathlib `IsSquare` in `ZMod p`); `F6_2_Q_infinite`: hence Q = ∞ for all five. The transfer uses Mathlib's Dirichlet theorem (`Nat.forall_exists_prime_gt_and_modEq`) and Jacobi symbols (reciprocity for n ≡ p ≡ 3 mod 4; `jacobiSym.mod_right'` for p ≡ q mod 4·∏ n). Outside Lean: nothing.
- Lean: [`F6_2.lean`](F6_2.lean) checks the mod-4 facts (`omega`) and all the mod-q
  translate facts (`decide`). Outside Lean: the transfer from f to primes p (reciprocity and
  Dirichlet; needs Mathlib).
- `certificate/f62_check.py` (second reader): the same facts from scratch. Scan script
  `verify.py` copied; the SAT calibration against the book's values is in
  `../open-problems/work/NT-F6.1/`.

**Review level.** `lean-proof`: proved in Lean + Mathlib ([`F6_2_mathlib.lean`](F6_2_mathlib.lean)).
**Prior art.** Partly known: the method (fix the quadratic character of small primes via reciprocity and Dirichlet to block a pattern) is classical (Lehmer & Lehmer, Proc. AMS 13 (1962); used in Guy F6 itself), but no source found proves these five patterns give ∞. Searched: web, Erdős Problems #436, Wright (J. Number Theory 2006; not read). 2026-11-04.
