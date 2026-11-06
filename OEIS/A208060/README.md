# OEIS A208060: lim a(n)^(1/n) = 2L, L the Lüroth geometric mean

**Source.** [A208060](https://oeis.org/A208060) (Paul D. Hanna): a(n) = 1 + 2n + 2^2 n[n/2] + 2^3 n[n/2][n/3] + ...,
[x] = floor(x). Conjecture in the entry: "limit a(n)^(1/n) = 2*L where L = 2.200161058099... is the geometric mean of
Luroth expansions, where log(L) = Sum_{n>=1} log(n)/(n*(n+1))". The companion
[A075885](https://oeis.org/A075885) (no factor 2^m) carries the same conjecture with limit L. (OEIS text, checked
2026-11-06.)

**Reading.** The m-th term is 2^m prod_{k=1..m} [n/k]; it vanishes for m > n, so a(n) = 1 + sum_{m=1..n} 2^m
prod_{k=1..m} [n/k]. The entry's %F line writes "Product_{k=1..m} 2^k*floor(n/k)", which gives a(2) = 21, not the data
term 13; it should read 2*floor(n/k). The %N definition reproduces the data (certificate/numeric.py).

**Result.** True: a(n)^(1/n) -> 2L. Likewise A075885(n)^(1/n) -> L. For any base c >= 1 the sum
1 + sum_m c^m prod_{k<=m}[n/k] has n-th root tending to cL.

**Argument.** Let T = 2^n P, P = prod_{k=1..n} [n/k] >= 1.
1. Each factor 2[n/k] (k <= n) is >= 1, so the m-th term grows with m up to m = n; hence T <= a(n) <= (n+1) T.
2. With d_j = log j - log(j-1) (d_1 = 0), log [n/k] = sum_{2 <= j <= [n/k]} d_j, and [n/k] >= j iff k <= [n/j], so
   log P = sum_{j=2..n} d_j [n/j].
3. n/j - 1 < [n/j] <= n/j, d_j >= 0 and sum_{j<=n} d_j = log n, so |log P / n - E(n)| <= log n / n with
   E(n) = sum_{j<=n} d_j / j.
4. Summation by parts: E(N) = sum_{j<N} log j / (j(j+1)) + log N / N, which tends to log L (the series converges since
   log j <= 2 sqrt j).
5. So (log a(n))/n -> log 2 + log L, as log(n+1)/n -> 0.

**Evidence.**
- Lean (Mathlib): [`A208060_mathlib.lean`](A208060_mathlib.lean). Main theorem `A208060_limit`:
  `Tendsto (fun n => (a n : ℝ) ^ (1 / n)) atTop (𝓝 (2 * exp (∑' j, log j / (j * (j + 1)))))`, with `a` the %N
  definition; also `A075885_limit` for `b n = 1 + ∑_{m ≤ n} ∏_{k ≤ m} n / k` and the base-c form `ag_limit`. Checked
  with `tools/leancheck-mathlib.sh`, no warnings, axioms propext, Classical.choice, Quot.sound. No sorry, no
  native_decide.
- [`certificate/numeric.py`](certificate/numeric.py): data terms a(0..9) and a(n)^(1/n) for n up to 10^4 (4.3987
  against 2L = 4.40026).
- Outside Lean: none. Not verified in Lean: agreement of `a` with the OEIS data terms (numeric.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: OEIS A208060 and A075885 (both still "Conjecture"), web search, 
google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs (neither has these entries). No proof found. The
argument is a standard Riemann-sum style estimate; the constant is Khinchin–Lüroth's L (Jager–de Vroedt).
