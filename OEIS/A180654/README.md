# OEIS A180654: Σ log(Σ_k C(n,k)^p x^k)^n/(n! n^n) is an integer e.g.f. (Conjectures 1-3)

**Source.** [A180654](https://oeis.org/A180654) (P. D. Hanna, Sep 2010). E.g.f. A(x) = Σ_{n≥0} log(Σ_{k=0..n} C(n,k)^2 x^k)^n
/(n! n^n). "Conjecture 1: this sequence consists entirely of integers." Conjecture 2: the same for C(n,k)^p,
every integer p ≥ 1. Conjecture 3: the same for C(n,k)^n. (OEIS text, CC BY-SA 4.0, rev #2 of Mar 30 2012,
read 2026-11-06.)

**Reading.** The %N line carries an extra factor x^n in each term; the example, the PARI program and the data
have none. The data follow the version without x^n (certificate/check_data.py). The result below holds for
both readings, because x^n = n!·(x^n/n!) is itself an integer e.g.f.

**Result.** All three conjectures are true. More generally: if P_n ∈ 1 + xℤ[x] and n divides k·[x^k]P_n for
all k, then Σ_n log(P_n)^n/(n! n^n) has integer e.g.f. coefficients.

**Argument.** Let H be the ring of integer e.g.f.s, {Σ a_N x^N/N! : a_N ∈ ℤ} (closed under products by
binomial convolution).
1. k C(n,k) = n C(n-1,k-1), so x P_n' = Σ_k k C(n,k)^p x^k = n Q_n with Q_n ∈ ℤ[x] (p ≥ 1, also p = n). Since
   P_n(0) = 1, 1/P_n ∈ ℤ[[x]], so x P_n'/P_n = n Σ d_N x^N with d_N ∈ ℤ, and
   g_n := log(P_n)/n = Σ_{N≥1} (d_N/N) x^N = Σ (N-1)! d_N x^N/N! ∈ xH.
2. For g ∈ xH, g^n/n! ∈ H: N![x^N] g^n/n! = Σ over set partitions of {1..N} into n blocks of Π_B b_{|B|}
   (b_j = j![x^j]g), an integer.
3. The n-th term log(P_n)^n/(n! n^n) = g_n^n/n! ∈ H and has x-order ≥ n, so the sum converges in H.
For p = 1, P_n = (1+x)^n gives Σ log(1+x)^n/n! = 1+x, the entry's comparison.

**Evidence.**
- [`certificate/check_data.py`](certificate/check_data.py): exact a(n), n ≤ 30, for p = 1, 2, 3 and C(n,k)^n;
  integral; p = 2 matches the data.
- [`certificate/check_terms.py`](certificate/check_terms.py): each term and each log(P_n)/n separately is an
  integer e.g.f. (n ≤ 8, p = 2, 3, to x^26).
- [`certificate/check_general.py`](certificate/check_general.py): random families with n | k[x^k]P_n: integral.
- [`certificate/check_name_reading.py`](certificate/check_name_reading.py): the %N reading (extra x^n) is also integral.
- Lean (Mathlib): [`A180654_mathlib.lean`](A180654_mathlib.lean), namespace `A180654`. Main theorem
  `A180654_general e he N : ∃ z : ℤ, aSeq e N = z` for P_n(k) = C(n,k)^(e n) with e n ≥ 1, where
  `aSeq e N = N! [x^N] Σ_{n≤N} logS(P_n)^n/(n! n^n)` (the PARI sum); corollaries `A180654_conj1` (p = 2),
  `A180654_conj2` (all p ≥ 1), `A180654_conj3` (C(n,k)^n). Steps `Pn_dvd`, `ell_dvd` (step 1), `step`,
  `divpow` (step 2, via θ = x d/dx), `term_hur`. `tools/leancheck-mathlib.sh`: OK, no warnings, axioms at most
  propext, Classical.choice, Quot.sound.
- Outside Lean: only the reading of log P as `logS P`, the series L with L(0) = 0 and x L' P = x P'
  (coefficient recurrence `ell`), and data agreement (check_data.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: entry still says "Conjecture"; web search found no proof; not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones).
