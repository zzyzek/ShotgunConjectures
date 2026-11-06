# OEIS A156834 and A156833: for n > 1, a(n) = n iff n is prime

**Source.** [A156834](https://oeis.org/A156834) = A156348 * A000010 and [A156833](https://oeis.org/A156833) =
A054525 * A156348 * [1, 2, 3, ...], both by Gary W. Adamson (Feb 2009). Both entries: "Conjecture: for n>1, a(n) = n
iff n is prime." A156348(n, k) = C(n/k - 2 + k, k - 1) if k | n (else 0); A054525(n, k) = mu(n/k) if k | n (else 0).
A156834 has the formula a(n) = Sum_{d|n} phi(d) C(d + n/d - 2, d - 1) (Seiichi Manyama, 2021). (OEIS text, entries
revision #20 of Jun 02 2025 and #11 of Jul 22 2025, checked 2026-11-06.)

**Result.** Both conjectures are true: for n > 1, A156834(n) >= n and A156833(n) >= n, with equality iff n is prime.

**Argument.** Write C_k(e) = C(e + k - 2, k - 1), so A156348(n, k) = C_k(n/k) for k | n.

1. *A156834.* a(n) = sum_{k | n} phi(k) C_k(n/k). Every C_k(e) >= 1 and sum_{k | n} phi(k) = n, so a(n) >= n. For
   prime p the divisors give 1 + (p - 1) = p. For composite n take k | n with 1 < k < n; then n/k >= 2 and
   C_k(n/k) >= C(k, k - 1) = k >= 2, so the term phi(k) C_k(n/k) exceeds phi(k) and a(n) > n.
2. *A156833.* a(n) = sum_{j | n} mu(n/j) sum_{k | j} k C_k(j/k). Put j = k e: a(n) = sum_{k | n} k I(k, n/k) with
   I(k, M) = sum_{e | M} mu(M/e) C_k(e). Then I(k, 1) = 1; I(1, M) = sum_{d | M} mu(d) = 0 for M > 1; and for k >= 2,
   (k - 1)! C_k(e) = e (e + 1) ... (e + k - 2) = sum_r c_r e^r with natural c_r and c_{k-1} = 1, so
   (k - 1)! I(k, M) = sum_r c_r J_r(M) with the Jordan totients J_r(M) = sum_{e | M} mu(M/e) e^r = M^r prod_{p | M}
   (1 - p^-r), which are >= 0 and > 0 for r >= 1. Hence I(k, M) > 0 for k >= 2. The k = n term gives n, the k = 1 term
   gives 0, every other term is > 0. So a(p) = p for primes and a(n) > n for composite n.

**Evidence.**
- Lean (Mathlib): [`A156834_mathlib.lean`](A156834_mathlib.lean), namespace `A156834`. `a834`, `a833` are the matrix
  products of the entries, with `T` = A156348 and `Mu` = A054525. Main theorems `A156834_conj` and `A156833_conj`:
  `1 < n → (a n = n ↔ n.Prime)`. Route: `a834_eq`; `a833_eq1`, `a833_eq` (regrouping j = k e); `I_one`,
  `I_at_one`, `I_pos` (rising factorial as Mathlib's `ascPochhammer`, leading coefficient 1); `J_nonneg`, `J_pos`
  (multiplicativity of mu * pow r, value p^((b+1)r) - p^(br) at prime powers, `J_prime_pow`). Check:
  `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms of every theorem propext, Classical.choice, Quot.sound.
  No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): both definitions reproduce the entries' data (n = 1..51) and the
  claim holds for n < 400.
- Outside Lean: none. Not verified in Lean: agreement of the definitions with the OEIS data terms (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: both entries still say "Conjecture"; no proof found by web search; not in
google-deepmind/formal-conjectures (clone of 2026-11-06) or otoi-lab/oeis-lean-proofs (clone of 2026-10-13). For
A156834 the proof is immediate from Manyama's divisor-sum formula (2021) and sum phi(d) = n. For A156833 the
positivity of the Moebius-transformed binomials via Jordan totients is ours.
