# OEIS A228456: the Hankel determinants are positive and odd

**Source.** [A228456](https://oeis.org/A228456) (Zhi-Wei Sun): a(n) = det[A086618(i+j)]_{0<=i,j<=n}, where
A086618(n) = s(n) = sum_k C(n,k)^2 C_k and C_k are the Catalan numbers. Conjecture (i) in the entry: "a(n) is always
positive and odd, and not congruent to 7 modulo 8." (OEIS text checked 2026-11-08; b-file to n = 53.)

**Result.** a(n) > 0 and a(n) is odd for every n >= 0. The clause "not 7 mod 8" is not settled; it holds for
n <= 300 (a(n) mod 8 takes the values 1, 3, 5 there). Conjecture (ii) (congruences mod p^2) is not addressed.

**Argument.**
1. *Positivity.* For t >= 0, sum_k C(n,k)^2 t^k is the constant term of the Laurent polynomial
   ((1+z)(1+t/z))^n. Taking the constant term on the circle |z| = sqrt(t) gives
   sum_k C(n,k)^2 t^k = (1/2pi) int_0^{2pi} (1 + t + 2 sqrt(t) cos(theta))^n d(theta), and the base is
   >= (1 - sqrt t)^2 >= 0. The Catalan numbers are the moments of the Marchenko-Pastur law
   mu(dt) = sqrt(t(4-t))/(2 pi t) dt on [0,4]. So s(n) = int x^n d(nu), where nu is the image of
   mu x (d(theta)/2pi) under (t, theta) -> 1 + t + 2 sqrt(t) cos(theta), a probability measure on [0,9] with a
   density, hence infinite support. a(n) is the Gram determinant of 1, x, ..., x^n in L^2(nu), which is positive
   because these functions are linearly independent in L^2(nu).
2. *Oddness.* Mod 2, C(n,k)^2 = C(n,k), C_k is odd iff k = 2^j - 1, and by Lucas C(n, 2^j - 1) is odd iff
   2^j | n+1. So s(n) = 1 + v_2(n+1) mod 2, i.e. s mod 2 = 1011101010111011... is the period-doubling sequence d
   (fixed point of 1 -> 10, 0 -> 11). Hence a(n) = Delta_d(n+1) mod 2, the (n+1) x (n+1) Hankel determinant of d,
   which is odd for every order by Allouche, Peyriere, Wen and Wen (Ann. Inst. Fourier 48 (1998), Prop. 2.2),
   as cited by Fokkink, Kraaikamp and Shallit (arXiv:1511.06569).
3. *Mod 8.* certificate/h8.py computes a(n) mod 8 by unit-pivot elimination over Z/8 (valid because the matrix is
   invertible mod 2 by step 2) for n <= 300, using the D-finite recurrence of A086618 checked against the sum.

**Evidence.**
- Lean (Mathlib): [`A228456_mathlib.lean`](A228456_mathlib.lean), theorem `A228456_pos`: 0 < det[s(i+j)] for all n,
  with s(n) = sum_k C(n,k)^2 catalan k. Route: the moments are constant terms, s(n) = CT(L^n V)/2 with
  L = (1 + wz)(1 + w/z), w = y + 1/y, V = (y - 1/y)(1/y - y) (`ct_L_pow`); the Hankel quadratic form is half the
  sum of squared coefficients of (sum c_i L^i)(y - 1/y) (`ct_mul_refl_pos`, `indep`). This is the constant-term
  form of step 1. Checked with tools/leancheck-mathlib.sh; axioms propext, Classical.choice, Quot.sound.
- Outside Lean: step 2 (oddness). It rests on Allouche-Peyriere-Wen-Wen 1998, Prop. 2.2 (Hankel determinants of the
  period-doubling sequence are odd), a published theorem with its own mod-2 continued-fraction proof, cited and not
  formalised; the identification s mod 2 = period-doubling is by hand (Lucas, Catalan parity) and checked by h8.py
  for n <= 600. Step 3 (mod 8, n <= 300) is a Python computation.

**Review level.** Positivity Lean-checked; oddness by hand plus citation; mod-8 data numerical.

**Prior art.** OEIS entry (conjecture still listed), Sun's arXiv papers linked there, web search on Hankel
determinants of A086618 and of the period-doubling sequence, google-deepmind/formal-conjectures (no A228456 file),
checked 2026-11-08. The positivity and oddness proofs are ours; the oddness rests on APWW's theorem.
