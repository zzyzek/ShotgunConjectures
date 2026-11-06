# OEIS A183129, A183128, A181084, A181082, A181080, A181078, A181076, A181074, A181070: binomial-power Hanna series are integer series

**Source.** Nine entries by P. D. Hanna (Oct-Dec 2010), each "Conjecture: this sequence consists entirely
of integers." (OEIS text, CC BY-SA 4.0, read 2026-11-06). Each is
A(x) = exp( Σ_{n≥1} [Σ_k B(n,k)^(e(n,k)) x^k] x^n/n ) with

| id | B(n,k) | e(n,k) |
|---|---|---|
| A181070 | C(n,k), k ≤ n | k+1 |
| A181080 | C(n,k), k ≤ n | n-k+1 |
| A181082 | C(n,k), k ≤ n | n+k |
| A181084 | C(n,k), k ≤ n | n+k+1 |
| A181074 | C(n+k-1,k), k ≥ 0 | k+1 |
| A181076 | C(n+k-1,k) | n |
| A181078 | C(n+k-1,k) | n+k-1 |
| A183128 | C(n+k-1,k) | k^2+1 |
| A183129 | C(n+k-1,k) | k^2+k |

**Result.** All nine are integer series. The argument also explains the entries' remarks that the
variants with exponent k, n-k, k^2 are not integral (they violate condition (E2) below).

**Argument.** Read the series as G(x, x) with G(x, y) = exp(Σ_{n≥1,k} ℓ(n,k) x^n y^k),
ℓ(n,k) = B(n,k)^e(n,k)/n. Group the monomials by primitive w = (n0, k0) (gcd 1, n0 ≥ 1): with
(n,k) = j w and β_w(j) = j ℓ(jw) = B(jw)^e(jw)/n0, G = Π_w E_w(x^n0 y^k0), E_w(t) = exp(Σ_j β_w(j) t^j/j).
If every β_w is an integer sequence with Gauss congruences β(mp^a) ≡ β(mp^(a-1)) (mod p^a), Dwork's lemma
gives E_w ∈ ℤ[[t]], so G ∈ ℤ[[x, y]] and A(x) = G(x, x) ∈ ℤ[[x]] (the product converges since n0 ≥ 1).

Fix w, write b(j) = B(jw), s = v_p(n0), M = m p^(a-1), N = m p^a.
- (Gauss for b.) b(j) = CT(Λ^j) with Λ = (1+x)^n0 x^(-k0) (first type) or Λ = (1-x)^(-n0) x^(-k0) (second
  type, C(n+k-1,k) = [x^k](1-x)^(-n)), Λ ∈ ℤ((x)). Frobenius gives Λ^p ≡ Λ(x^p) (mod p), lifting gives
  Λ^N ≡ Λ(x^p)^M (mod p^a), and CT(Λ(x^p)^M) = CT(Λ^M). So b(N) ≡ b(M) (mod p^a).
- (Valuation.) v_p(b(j)) ≥ s: first type from C(n,k) gcd(n,k)/n ∈ ℤ; second type from
  C(jN0-1, jk0) = C(jN0, jk0) n0/N0 with N0 = n0 + k0, gcd(N0, k0) = 1.
- If k0 = 0 then n0 = 1 and b ≡ 1. Let k0 ≥ 1. Conditions on e, checked for all nine:
  (E1) e(jw) ≥ 1; (E2) e(Mw) ≥ a + 1 (≥ a suffices when s = 0) and e(Nw) ≥ e(Mw);
  (E3) φ(p^a) | e(Nw) - e(Mw) (e is linear or quadratic homogeneous-plus-constant in j:
  differences are multiples of m p^(a-1)(p-1) or m^2 p^(2a-2)(p^2-1)).
- s ≥ 1: v_p(β(M)), v_p(β(N)) ≥ s(a+1) - s ≥ a, both ≡ 0. s = 0, p | b(M): then p | b(N) and both
  b^e ≡ 0 (mod p^a) by (E2). s = 0, p ∤ b(M): b(N)^e(N) ≡ b(M)^e(N) = b(M)^e(M) b(M)^(e(N)-e(M)) ≡ b(M)^e(M)
  by Euler and (E3). Integrality of β from the valuation bound and (E1).
- (E2) for each: M ≥ p^(a-1) ≥ a, so M k0 + 1 ≥ a + 1 (k+1, k^2+1, k^2+k, n+k+1, n-k+1 when n0 > k0;
  n0 = k0 forces w = (1,1), b ≡ 1); n+k: M(n0+k0) ≥ 2p^(a-1) ≥ a+1; n+k-1: if s ≥ 1 then n0 ≥ 2 and
  3p^(a-1) - 1 ≥ a+1, if s = 0 then 2p^(a-1) - 1 ≥ a; n: if s ≥ 1 then M n0 ≥ p^a ≥ a+1, if s = 0 then
  M n0 ≥ a.

**Evidence.**
- [`certificate/check.py`](certificate/check.py): all nine series exact to x^24, integral, match the data;
  Gauss congruences of β_w for n0 ≤ 6, k0 ≤ 6, p ≤ 13, m p^a ≤ 40; the four "NOT integral" variants
  in the entries fail both, as predicted.
- Lean (Mathlib): [`A183129_mathlib.lean`](A183129_mathlib.lean), namespace `A183129`, all nine series:
  `A181070_int`, `A181074_int`, `A181076_int`, `A181078_int`, `A181080_int`, `A181082_int`, `A181084_int`,
  `A183128_int`, `A183129_int`, each `∀ n, ∃ z : ℤ, a n = z` for the coefficients of
  exp(Σ_n [Σ_k B(n,k)^e(n,k) x^k] x^n/n). Route: B(n,k) = [x^(n+k)] (x f)^n with f = 1 + x or the truncated
  geometric series, the library power-family lemma `Tpow_gauss` in [`lib/OpenProblemsLib/DworkEuler.lean`](../../lib/OpenProblemsLib/DworkEuler.lean) (Frobenius congruences in place of the
  constant-term argument; conditions (E1)-(E3) become `gcond_of`: e(pn,pk) - 1 = e(n,k) - 1 + (p-1)L with
  p^t ∣ L, and e - 1 ≥ k, n - k or v_p(n)), then `recSeq_int`. Check `tools/leancheck-mathlib.sh`: OK, no
  warnings, axioms propext, Classical.choice, Quot.sound; no `sorry`, no `native_decide`.
- Outside Lean: the reading of exp(...) as the coefficient recurrence (standard) and the data agreement
  (check.py).

**Review level.** `lean-proof` (all nine).

**Prior art.** Checked 2026-11-06: the entries still say "Conjecture"; web search found the entries and
S. Fried, arXiv:2607.24832 (which treats A158110, not these); none of the nine A-numbers is in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones). Tools (Dwork's lemma,
Gauss congruences of constant terms of powers of a Laurent series) are standard.
