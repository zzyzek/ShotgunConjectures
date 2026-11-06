# OEIS A209998: penultimate term of row n equals A199923(n)

**Source.** [A209998](https://oeis.org/A209998) (Clark Kimberling, 2012): triangle of coefficients of v(n,x), with
u(1,x) = v(1,x) = 1, u(n,x) = x u(n-1,x) + 2x v(n-1,x) + 1, v(n,x) = (x+1) u(n-1,x) + 2x v(n-1,x) + 1.
"Conjecture: penultimate term in row n is A199923(n)." [A199923](https://oeis.org/A199923)(n) =
Sum_{k=0..3^(n-1)} gcd(k, 3^(n-1)), a(0) = 1. (OEIS text, CC BY-SA 4.0, revision #8, checked 2026-11-06.)

**Reading.** The %F lines print the v-recursion with x*v(n-1,x); the entry's Mathematica program and the data use
2x*v(n-1,x) (row 2 is "2 3", which only the 2x version gives). We use the program's recursion. Row n has
n entries (v(n,x) has degree n-1) and ends with 3^(n-1), as the entry says.

**Result.** Misstated by one index. The penultimate term of row n is A199923(n-1) = 2(n+1)3^(n-3) for every
n >= 2 (proved). As printed (A199923(n)) it fails already at row 2: penultimate term 2, A199923(2) = 8.

**Argument.** Write U_n, V_n for the x^(n-1) coefficients and U'_n, V'_n for the x^(n-2) coefficients of u(n,x),
v(n,x). Comparing coefficients: U_n = V_n = U_(n-1) + 2V_(n-1), so U_n = V_n = 3^(n-1); and
U'_n = U'_(n-1) + 2V'_(n-1), V'_n = U'_(n-1) + U_(n-1) + 2V'_(n-1), with U'_2 = 1, V'_2 = 2. Induction gives
U'_n = (2n-1)3^(n-3) and V'_n = 2(n+1)3^(n-3). For A199923: G_m = Sum_{k<3^m} gcd(k, 3^m) satisfies
G_(m+1) = 2*3^m + 3 G_m (group k by k mod 3), so G_m = (2m+3)3^(m-1), and A199923(m+1) = G_m + 3^m
= 2(m+3)3^(m-1) (S. Irvine's formula a(n) = 2(n+2)3^(n-2)). With m = n-2 this is V'_n.

**Evidence.**
- Lean (Mathlib): [`A209998_mathlib.lean`](A209998_mathlib.lean). `u k`, `v k` are u(k+1,x), v(k+1,x) in
  `ℤ[X]`; `A199923` is the gcd-sum definition. Theorems `A209998.A209998_corrected (j) : (v (j+1)).natDegree =
  j+1 ∧ (v (j+1)).coeff j = A199923 (j+1)` (row n = j+2), `A209998.A209998_literal_false`,
  `A209998.A199923_formula`. Route: `cu`, `cv`, `vanish`, `top`, `second`, `natDegree_v`, `G_rec`, `G_eq`.
  Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms propext, Classical.choice, Quot.sound. No
  `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py) ([`check.out`](certificate/check.out)): the recursion reproduces
  the 55 data terms; penultimate terms equal A199923(n-1) for n = 2..11.
- Outside Lean: none. Not verified in Lean: agreement with the OEIS data (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry lists the claim as a conjecture; A199923's closed form is Irvine's
(2022) and Greubel's (2023) formula, without a proof in the entry. Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs.
