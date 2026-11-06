# OEIS A181316: exp(Σ (q-1)((q^n-1)/(q-1))^(n-1) x^n/n) is an integer series for every q > 1

**Source.** [A181316](https://oeis.org/A181316) (Paul D. Hanna, Oct 31 2010): g.f. A(x) = exp(Sum_{n>=1}
2*((3^n-1)/2)^(n-1)*x^n/n). "Conjecture: exp( Sum_{n>=1} (q-1)*((q^n-1)/(q-1))^(n-1)*x^n/n ) is an integer series
for all integer q>1." (OEIS text, revision #2 of Mar 30 2012, checked 2026-11-06.)

**Result.** True for every integer q >= 2.

**Argument.** Write c(n) = (q^n - 1)/(q - 1) = 1 + q + ... + q^(n-1) and b(n) = (q-1) c(n)^(n-1). By the Dold/Gauss
criterion it suffices that b(N) ≡ b(M) (mod p^a) whenever N = m p^a, M = m p^(a-1), a >= 1. Note c(N) = c(M) (1 +
q^M + ... + q^(M(p-1))), so p | c(M) implies p | c(N); and x^N ≡ x^M (mod p^a) for every integer x.
1. p ∤ c(M), p ∤ q - 1: (q - 1)(c(N) - c(M)) = q^N - q^M ≡ 0, so c(N) ≡ c(M) (mod p^a). Also c(M)^M (c(M)^(N-M) - 1)
   ≡ 0, so c(M)^(N-M) ≡ 1. Hence c(N)^(N-1) ≡ c(M)^(N-1) = c(M)^(M-1) c(M)^(N-M) ≡ c(M)^(M-1).
2. p ∤ c(M), p | q - 1: c(M) ≡ M (mod p), so p ∤ M, which forces a = 1; both b(N), b(M) contain the factor q - 1.
3. p | c(M): then M >= 2, b(N) has the factor c(N)^(N-1) with N - 1 >= a, and b(M) the factor c(M)^(M-1) with
   M - 1 >= a, except for p = 2, a = 2, M = 2; there q is odd and b(2) = (q-1)(q+1) is divisible by 4.
The Gauss congruences give integers e(d) with b(n) = Σ_{d|n} d e(d), so the series is Π_d (1 - x^d)^(-e(d)).

**Evidence.**
- Lean (Mathlib): [`A181316_mathlib.lean`](A181316_mathlib.lean), namespace `A181316`. Main theorem
  `A181316_conjecture (q : ℤ) (hq : 2 ≤ q) (n : ℕ) : ∃ z : ℤ, expCoeff (bq q) n = z`, with
  `bq q n = (q-1) * ((q^n-1)/(q-1))^(n-1)` (the entry's formula) and `expCoeff` the coefficients of
  exp(Σ b(n) x^n/n) via the recurrence (n+1) A(n+1) = Σ b(j+1) A(n-j); `A181316_int` is q = 3. Route: `LG_b` (steps
  1-3, with `pow_gauss`, `c_split`, `c_sub_self_dvd`), then `dwork` and `expCoeff_int_of_euler`, copied from
  [`../A207969/A207969_mathlib.lean`](../A207969/A207969_mathlib.lean). Check: `tools/leancheck-mathlib.sh`, exit
  0, no warnings; axioms at most propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): exact rational series for q = 2..8 up to x^40 are integral, the
  Gauss congruences hold on a grid, and the q = 3 series reproduces the data.
- Outside Lean: none beyond the reading of exp(...) as the recurrence (standard), and data agreement (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: the entry still says "Conjecture"; web search found no proof; not in
google-deepmind/formal-conjectures (clone of 2026-11-06) or otoi-lab/oeis-lean-proofs (clone of 2026-10-13). The
companion A180606 (exp(Σ (2^n-1)^(n-1) x^n/n)) is a different series. The method is the standard Gauss-congruence
criterion; the congruence for this b(n) is ours.
