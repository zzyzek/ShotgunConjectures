# OEIS A176827: the q-analogue a(n,q) is an integer for every positive integer q

**Source.** [A176827](https://oeis.org/A176827) (P. D. Hanna, Apr 2010): A(x,q) = Σ a(n,q) x^n/q^(n(n-1)/2)
with A(x,q) = exp(Σ_{n≥1} A(x/q^n, q)^n x^n/n). "Conjecture: {a(n,q), n>=0} are integers when q is a positive
integer." (OEIS text, CC BY-SA 4.0, rev #2 of Mar 30 2012, read 2026-11-06.) The entry's second conjecture,
a(n,q) ≡ 1 (mod q), is not treated here (it holds numerically, see Evidence).

**Result.** True: a(n,q) ∈ ℤ for all n ≥ 0 and integers q ≥ 1.

**Argument.** Write A_N = [x^N] A, so a(N,q) = q^(C(N,2)) A_N. Fix a prime p.

1. *p ∤ q.* Put r = 1/q ∈ ℤ_(p). The log of A is Φ(log G) with G(x, y) = 1/(1 - y x A(x)) and Φ the linear map
   x^m y^n ↦ r^(n(m-n)) x^m (m ≥ n), because [x^m](x A(r^n x))^n = r^(n(m-n)) [x^m](xA)^n. If A ∈ ℤ_(p)[[x]] up
   to degree N-1, then G is p-integral up to that degree; factor G = Π_v (1 - x^v y^w)^(e_v) with e_v ∈ ℤ_(p);
   then exp(Φ log G) = Π_v E_v^(-e_v), E_v(t) = exp(Σ_j r^(j^2 c_v) t^j/j) with c_v = w(v-w) ≥ 0, and
   E_v ∈ ℤ_(p)[[t]] by the Dieudonné-Dwork criterion: j ↦ r^(c j^2) satisfies r^(c m^2 p^(2a)) ≡ r^(c m^2 p^(2a-2))
   (mod p^a) (Euler for r a unit). So A_N ∈ ℤ_(p), hence a(N,q) ∈ ℤ_(p). (Same lemma as for A157675 in
   [../A183241/README.md](../A183241/README.md).)
2. *p | q,* v = v_p(q) ≥ 1. Claim v_p(A_N) ≥ -v C(N,2). Induction on N. The log coefficient is
   L_N = Σ_n (1/n) Σ_{M_1+...+M_n = N-n} Π_i A_{M_i} q^(-n M_i). With K = N - n and the induction hypothesis,
   each product has valuation ≥ -v(Σ C(M_i,2) + nK), and C(N,2) = C(n,2) + nK + C(K,2) ≥ C(n,2) + nK + Σ C(M_i,2),
   so v_p(L_N) ≥ -v C(N,2) + v C(n,2) - v_p(n) ≥ -v C(N,2) (C(n,2) ≥ v_p(n) for n ≥ 1). Then
   A_N = Σ_k (1/k!) Σ_{N_1+...+N_k=N} Π L_{N_i}, and C(N,2) - Σ C(N_i,2) = Σ_{i<j} N_i N_j ≥ C(k,2) ≥ v_p(k!), so
   v_p(A_N) ≥ -v C(N,2). Hence a(N,q) ∈ ℤ_(p).

**Evidence.**
- [`certificate/check.py`](certificate/check.py): exact a(n,q) for q ∈ {2,3,4,5,6,8,9,10,12}, n ≤ 11: all
  integers, all ≡ 1 (mod q); q = 3 matches the data.
- Lean: none. Outside Lean: the whole argument.

**Review level.** `rechecked`.

**Prior art.** Checked 2026-11-06: entry still says "Conjecture"; web search found no proof; not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones).
