# OEIS A127750 / A127749: row sums mod 2 are the Fredholm-Rueppel sequence

**Source.** [A127749](https://oeis.org/A127749) (Paul Barry, Jan 28 2007): "Inverse of number
triangle A(n,k) = 1/(2n+1) if k <= n <= 2k, 0 otherwise." Comment: "Conjectures: row sums modulo 2
are the Fredholm-Rueppel sequence A036987; row sums of triangle modulo 2 are A111982. Row sums are
A127750." [A127750](https://oeis.org/A127750): row sums of A127749; "Conjecture: a(n) mod 2 gives
Fredholm-Rueppel sequence A036987" (verified to n = 2048 by A. Karttunen, 2018). R. J. Mathar (2021)
notes A127749(n,k) = (2k+1) A111967(n,k), A111967 the inverse of the 0/1 triangle
[k <= n <= 2k] (A101688), and that the first conjecture is equivalent to the conjectured row sums
of A111967. (OEIS text CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** A036987(n) = 1 if n = 2^m - 1, else 0. "Row sums of triangle modulo 2" = the sum over
k of (A127749(n,k) mod 2), compared with A111982(n) = sum over k of |A111967(n,k)|.

**Result.** Both conjectures are true, and so is the A111967 row-sum conjecture: the row sums of
A111967 are exactly A036987, and every entry of A111967 is -1, 0 or 1.

**Argument.** Let M(n,k) = [k <= n <= 2k]. Its inverse t (A111967) satisfies, for each column k,
sum_{j = ceil(n/2)..n} t(j,k) = [n = k]. Comparing the windows for n and n - 1 gives the recursion
t(n,k) = [n = k] - [n - 1 = k] + [n odd] t((n-1)/2, k), t(0,k) = [k = 0]. Hence t is lower
triangular, column k reads 1 at row k, -1 at row k + 1 (k > 0), and below that copies
t(n,k) = t((n-1)/2,k) for odd n and 0 for even n; so all entries are -1, 0, 1. Row sums
R(n) = sum_k t(n,k) satisfy R(0) = 1, R(n) = [n odd] R((n-1)/2), so R(n) = 1 exactly when
n + 1 is a power of 2. A127749 = t times diag(2k+1) (inverse of diag(1/(2n+1)) M), so
A127750(n) = R(n) + 2 sum_k k t(n,k) ≡ R(n) (mod 2), and (2k+1) t(n,k) mod 2 = |t(n,k)|.

**Evidence.**
- Lean (Mathlib): [`A127750_mathlib.lean`](A127750_mathlib.lean). `T_inverse` (T = (2k+1) t is the
  inverse of B(n,k) = [k <= n <= 2k]/(2n+1)) and `T_unique` (the only one), `t_inverse`,
  `t_unique` (t is A111967). Main theorems `A127750_mod_two` (A127750 n % 2 = A036987 n),
  `A127749_rowsum_mod_two` (sum of T n k % 2 = A111982 n), plus `rowsum_t`, `t_values`.
  Axioms propext, Classical.choice, Quot.sound; no `sorry`, no `native_decide`, no warnings.
- [`certificate/check.py`](certificate/check.py): the recursion reproduces the OEIS data of
  A127749, A127750, A111982 and is the exact inverse for n, k <= 200.
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: entries and histories of A127749, A127750, A111967, A111982
(conjectures still open there; A111982's own comment states the parity fact without proof);
web search; not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (grep A127749,
A127750, A111967). No proof found.
