# OEIS A202150 / A202146: the odd coefficients of the q-analog of π/2 sit exactly at 3n(n+1)

**Source.** [A202150](https://oeis.org/A202150) (Paul D. Hanna), "a(n) = A202146(3*n*(n+1)) for n>=0."
Comment: "Conjecture: this sequence consists of all odd terms in A202146; the g.f. of A202146 is
1/(1-x) + Sum_{n>=1} x^n/(1-x) * Product_{k=1..n} (1 - x^k) / (1 - x^(2*k+1)), which by the conjecture has an
odd coefficient of x^m iff m = 3*n*(n+1) for n>=0. The conjecture holds for at least the initial 30300 terms
of A202146." [A202146](https://oeis.org/A202146) repeats the parity claim as a conjectured formula. (OEIS text,
CC BY-SA 4.0, checked 2026-11-06.)

**Result.** True. With (a;q)_n = (1−a)(1−aq)···(1−aq^{n−1}), the g.f. of A202146 is
A(q) = Σ_{n≥0} q^n (q;q)_n/(q;q²)_{n+1}, and

(∗)  Σ_{n≥0} (−q)^n (−q;q)_n/(q;q²)_{n+1} = Σ_{m≥0} (−1)^m q^{3m(m+1)}.

Reducing mod 2 ((q;q)_n ≡ (−q;q)_n, q^n ≡ (−q)^n, and 1/(q;q²)_{n+1} has integer coefficients) gives
A(q) ≡ Σ_m q^{3m(m+1)} (mod 2): A202146(k) is odd iff k = 3m(m+1), so A202150 lists exactly the odd terms.

**Argument.**
1. *Finite identities.* Let E_b(n) = Σ_{j∈ℤ} (−1)^j q^{3j²+bj} [2n+1, n−2j] (Gaussian binomials, zero outside
   0..2n+1). Expanding [2n+3, k+1] by the two q-Pascal rules in the two orders,
   [N+2,k+1] = [N,k−1] + (q^k+q^{k+1})[N,k] + q^{2k+2}[N,k+1] and
   [N+2,k+1] = q^{N+1−k}[N,k−1] + (1+q^{N+1})[N,k] + q^{k+1}[N,k+1],
   and folding odd offsets back with [N,k] = [N,N−k], one gets for N = 2n+1
   E_b(n+1) = −q^{3−b}E_{6−b}(n) + (1+q)q^n E_{b−2}(n) + q^{2n+2}E_{4−b}(n) and
   E_b(n+1) = (1+q^{2n+2})E_b(n) + q^{n+1}E_{2−b}(n) − q^{n+3−b}E_{4−b}(n).
   The second at b = 1 and the first at b = 3 involve only E_1, E_3; induction from E_1(0) = E_3(0) = 1 gives
   E_1(n) = (−q;q)_n and E_3(n) = q^n(−q;q)_n.
2. *Bailey pair.* E_1(n) + E_3(n) = (−q;q)_n(1+q^n) says exactly that (α_n, β_n) is a Bailey pair relative to
   a = q, with β_n = (−q;q)_n(1+q^n)/(2(q;q)_{2n+1}), 2(1−q)α_0 = 2,
   2(1−q)α_{2m} = (−1)^m q^{m(3m+1)}(1+q^{2m}) (m ≥ 1), 2(1−q)α_{2m+1} = (−1)^{m+1} q^{3m(m+1)}(1+q^{2m+2}).
3. *Bailey's lemma* with a = q, ρ1 = q, ρ2 = −1 (so aq/ρ1ρ2 = −q): the left side is
   Σ (q)_n(−1)_n(−q)^n β_n = LHS(∗); the right side is (1−q)/(1+q)·Σ (−1)_n(−q)^n α_n/(−q²;q)_n. The factor
   (1+q^{n})(1+q^{n+1}) in the denominator cancels one of the two monomials of each α_n, and the remaining
   terms pair up (n = 2m and 2m+1) into (−1)^m q^{3m(m+1)}; the n = 0, 1 terms give 1/(1+q) + q/(1+q) = 1.

**Evidence.**
- [`certificate/check.py`](certificate/check.py): (∗) and the parity statement as power-series identities to degree
  1500; the OEIS b-file of A202146 (n ≤ 2106 available, 1501 terms compared) matches the g.f.; the finite
  identities E_1, E_3 for n ≤ 12 (sympy).
- Lean (Mathlib): [`A202150_mathlib.lean`](A202150_mathlib.lean), importing the library module
  `OpenProblemsLib.QSeries`. Main theorem `A202146_entry_parity`: the coefficient A202146(k) of the
  entry's g.f. (written literally, `A202146_entry`) is odd iff k = 3m(m+1). Route: the finite
  identities `E_closed` and the Bailey pair `bailey_pair` (step 1-2), identity (*) as `star`
  (step 3: the alpha_n regrouping is `TL_succ`, the interchange of sums `sum_TL`, the inner sums
  come from the library q-Gauss sum `qGaussSum_mul` for a = q, rho1 = q, rho2 = -1, proved there by
  a Gosper certificate for r = 0 and a Zeilberger certificate in r), `mod2_reduction`, and
  `A202146_entry_eq` (the entry's g.f. equals Sum q^n (q;q)_n/(q;q^2)_{n+1}).
  `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms propext, Classical.choice, Quot.sound.
  No `sorry`, no `native_decide`.
- Outside Lean: none. The only step not machine-checked is reading the entry's g.f. formula as the
  Lean definition `entryTerm`.

**Review level.** `lean-proof` (every step is in Lean; earlier the proof was re-derived step by step and
confirmed numerically).

**Prior art.** Checked 2026-11-06. Both entries still state the parity as a conjecture (A202150: checked to
30300 terms). Web search for the series and for identity (∗) (partial theta identities: Warnaar,
arXiv:math/0105002; Lovejoy, "Ramanujan-type partial theta identities and conjugate Bailey pairs"; Cigler,
arXiv:math/0610546) found neither (∗) nor the finite identities E_1, E_3 in this form. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (trees at HEAD 2026-11-06).
