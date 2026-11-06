# OEIS A163138: exp(Σ (q^n + A)^n x^n/n) = A is an integer series for every integer q

**Source.** [A163138](https://oeis.org/A163138) (P. D. Hanna, Aug 2009), A(x) = exp(Σ_{n≥1} (2^n + A(x))^n x^n/n).
"Conjecture: if q is an integer, then A(x,q) is a power series in x with integer coefficients." for
A(x,q) = exp(Σ (q^n + A(x,q))^n x^n/n). (OEIS text, CC BY-SA 4.0, rev #2 of Mar 30 2012, read 2026-11-06.)

**Result.** True for every integer q (q = 0: Catalan numbers, q = 1: large Schröder numbers, q = 2: A163138).

**Argument.** Three-variable form: with H(t, y, x) = 1/(1 - t(y + A(x))) = exp(Σ_n t^n (y + A)^n/n), the
log of A equals Φ(log H) where Φ is the linear map t^n y^r x^s ↦ q^(nr) x^(n+s): indeed
(y + A)^n = Σ_r C(n,r) y^r A^(n-r) and (q^n + A)^n = Σ_r C(n,r) q^(nr) A^(n-r). Monomials of H have r ≤ n and
n ≥ 1, so finitely many lie below any x-degree n+s; c(n, r) = nr is quadratic: c(jv) = j^2 c(v) ≥ 0.
If A is integral up to degree N-1, so is H (in the relevant range), and H = Π_v (1 - T^v)^(e_v), e_v ∈ ℤ.
Then exp(Φ log H) = Π_v E_v^(-e_v), E_v = exp(Σ_j q^(j^2 c_v) z^j/j) with z = x^(n_v + s_v). Each E_v is
integral by Dwork: β(j) = q^(c j^2) satisfies β(m p^a) ≡ β(m p^(a-1)) (mod p^a) (p ∤ q: Euler, since
φ(p^a) | c m^2 p^(2a-2)(p^2-1); p | q, c ≥ 1: both terms divisible by p^(p^(2a-2)) and p^(2a-2) ≥ a;
c = 0: constant). The degree-N coefficient of A depends only on lower coefficients, so A is integral by
induction. (Same lemma as in [../A183241/README.md](../A183241/README.md), item 4.)

**Evidence.**
- [`certificate/check.py`](certificate/check.py): exact A to x^12 for q ∈ {-3,...,3, 5, 6}: integral; q = 2
  matches the data, q = 0 Catalan, q = 1 Schröder.
- Lean (Mathlib): [`A163138_mathlib.lean`](A163138_mathlib.lean), namespace `A163138`. `a q` is defined from the
  functional equation (coefficients of exp(S), x S' read off Σ (q^n + A)^n x^n/n). Main theorems:
  `A163138_conjecture (q : ℤ) n : ∃ z : ℤ, a q n = z` and `A163138_int` (q = 2). The three-variable form is the
  library [`lib/OpenProblemsLib/DworkEuler.lean`](../../lib/OpenProblemsLib/DworkEuler.lean) with F = X (Y + A) ∈ ℤ[Y][X] evaluated at Y = q^n (`ycond_pow`), weights 1, then `rowB_gauss`,
  `recSeq_int`. Check `tools/leancheck-mathlib.sh`: OK, no warnings, axioms propext, Classical.choice,
  Quot.sound; no `sorry`, no `native_decide`.
- Outside Lean: the reading of exp(...) as the coefficient recurrence (standard) and the data agreement
  (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: entry still says "Conjecture"; web search found no proof; not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones).
