# OEIS A163921: G(x) = exp(Σ G(L(n) x)^n x^n/n) is integral whenever exp(Σ L(n) x^n/n) is

**Source.** [A163921](https://oeis.org/A163921) (P. D. Hanna, Sep 2009), g.f. A(x) = exp(Σ A(σ(n) x)^n x^n/n).
"Conjecture: if F(x) = exp( Sum_{n>=1} L(n)*x^n/n ) is an integer series, then the g.f. that satisfies:
G(x) = exp( Sum_{n>=1} G( L(n)*x )^n*x^n/n ) is also an integer series." (OEIS text, CC BY-SA 4.0, rev #2
of Mar 30 2012, read 2026-11-06.)

**Result.** True for every such L. A163921 (L = σ, with
exp(Σ σ(n) x^n/n) = Π_k (1 - x^k)^(-1)) and A157675 (L = 2^n) are special cases.

**Argument.**
1. F ∈ 1 + xℤ[[x]] ⟺ L(n) ∈ ℤ satisfies the Gauss congruences L(m p^a) ≡ L(m p^(a-1)) (mod p^a) (Dwork).
2. log G = Φ(log H) with H(x, y) = 1/(1 - y x G(x)) = exp(Σ_n y^n (xG)^n/n) and Φ the linear map
   x^m y^n ↦ L(n)^(m-n) x^m (m ≥ n ≥ 1), since [x^m](x G(L(n) x))^n = L(n)^(m-n) [x^m](xG)^n.
3. Suppose G is integral up to degree N-1; then so is H, and H = Π_{(m,n)} (1 - x^m y^n)^(e_(m,n)) with
   e ∈ ℤ. Group by primitive w = (m0, n0): log H = -Σ e_v Σ_j x^(jm) y^(jn)/j, and
   Φ(Σ_j x^(jm) y^(jn)/j) = Σ_j u(j)^(jc) x^(jm)/j with u(j) = L(jn), c = m - n ≥ 0.
4. β(j) = u(j)^(jc) satisfies Gauss congruences: u does (subsequence of L). Let M = m p^(a-1), N = m p^a.
   c = 0: β ≡ 1. If p ∤ u(M): u(N) ≡ u(M) (mod p^a) gives u(N)^(Nc) ≡ u(M)^(Nc), and
   u(M)^((N-M)c) ≡ 1 since φ(p^a) | m p^(a-1)(p-1)c. If p | u(M): p | u(N), and Mc ≥ p^(a-1) ≥ a, so both
   terms are ≡ 0 (mod p^a).
5. So each exp(Φ(Σ_j ...)) lies in ℤ[[x]] (Dwork), and exp(Φ log H) = Π_v E_v^(-e_v) is integral; its degree-N
   coefficient depends only on G below degree N, so G is integral up to degree N. Induction.

**Evidence.**
- [`certificate/check.py`](certificate/check.py): G exact to x^11 for L = σ (matches A163921 data), 2^n (matches
  A157675), C(2n,n), 3^n - (-2)^n, 6(-1)^n: all integral; L(n) = n + 1 (not a Gauss sequence) gives
  non-integers, as expected.
- Lean (Mathlib): [`A163921_mathlib.lean`](A163921_mathlib.lean), namespace `A163921`. `a L` is defined from the
  functional equation (coefficients of exp(S), x S' read off Σ G(L(n)x)^n x^n/n with `G(L(n)x)` the polynomial
  composition). Main theorems: `A163921_int n : ∃ z : ℤ, a sig n = z` (the entry, L = σ) and
  `A163921_conjecture L (hF : ∀ n, ∃ z : ℤ, expCoeff L n = z) n : ∃ z : ℤ, a L n = z` (the conjecture as stated).
  Steps 1-5 via the library [`lib/OpenProblemsLib/DworkEuler.lean`](../../lib/OpenProblemsLib/DworkEuler.lean) (`rowB_int`, `W1_pow` with W(m,n) = L(n)^(m-n), `recSeq_int`) and
  [`lib/OpenProblemsLib/Dwork.lean`](../../lib/OpenProblemsLib/Dwork.lean) (`gauss_of_expCoeff_int` for step 1,
  `LGp_of_euler` for σ). Check `tools/leancheck-mathlib.sh`: OK, no warnings, axioms propext, Classical.choice,
  Quot.sound; no `sorry`, no `native_decide`.
- Outside Lean: the reading of exp(...) as the coefficient recurrence (standard) and the data agreement
  (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: entry still says "Conjecture"; web search found no proof; not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones).
