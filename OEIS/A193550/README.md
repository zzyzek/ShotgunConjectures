# OEIS A193550: sqrt((A(x) - 1)/x) is an integer series

**Source.** [A193550](https://oeis.org/A193550) (Paul D. Hanna, 2011): o.g.f.
A(x) = 1/(1 - x/(1 - x/(1 - 9x/(1 - 9x/(1 - 25x/(1 - 25x/(1 - ...))))))), a continued fraction whose partial
numerators are the odd squares, each twice. "Conjecture: given o.g.f. A(x), then sqrt( (A(x) - 1)/x ) is an
integer series." The example reports integrality for the first 500 terms. (OEIS text, CC BY-SA 4.0,
revision #19, checked 2026-11-06.)

**Result.** True. Writing A = 1 + x B(x)^2, B has integer coefficients (B = 1 + x + 6x^2 + 97x^3 + ...). The
proof uses only that every partial numerator is 1 mod 4, so the same holds for any S-fraction
1/(1 - c_1 x/(1 - c_2 x/(1 - ...))) with all c_i = 1 (mod 4) integers.

**Argument.**
1. Each coefficient of a continued fraction 1/(1 - c_1 x/(1 - c_2 x/ ...)) is an integer polynomial in the
   c_i (the truncation of depth n+1 already gives the x^n coefficient). Reducing mod 4 with every c_i = 1 gives
   the all-ones fraction, whose series is the Catalan series C(x) = 1 + x C(x)^2. So a(n) = Catalan(n) (mod 4)
   for all n. In particular (A - 1)/x = C^2 + 4H with H in Z[[x]], and H(0) = (a(1) - 1)/4 = 0.
2. C is a unit of Z[[x]]. Put y = H / C^2, so y(0) = 0 and (A - 1)/x = C^2 (1 + 4y).
3. W + W^2 = y has a solution W in Z[[x]] with W(0) = 0: iterate w_0 = 0, w_(k+1) = y - w_k^2; then
   w_(k+1) - w_k = -(w_k - w_(k-1))(w_k + w_(k-1)) is divisible by x^(k+1), so the w_k converge x-adically.
4. B = C (1 + 2W) has B(0) = 1 and B^2 = C^2 (1 + 4(W + W^2)) = C^2 (1 + 4y) = (A - 1)/x.

**Evidence.**
- Lean (Mathlib): [`A193550_mathlib.lean`](A193550_mathlib.lean). `T m j` is the depth-m truncation from level j
  (`T (m+1) j = invOfUnit (1 - C (lam j) * X * T m (j+1)) 1`, `lam i = (2*(i/2)+1)^2`), and `a n` is the x^n
  coefficient of `T (n+1) 0`, as in the entry's PARI program; `a_eq_deeper` shows every deeper truncation has the
  same x^n coefficient. Main theorem `A193550.A193550_conjecture : ∃ B : PowerSeries ℤ, constantCoeff B = 1 ∧
  mk a = 1 + X * B ^ 2`. Route: `a_mod4` (via `mod4`, `Cb_eq`, `lam_mod`), `a_one`, `quad_root`, Mathlib's
  `catalanSeries_sq_mul_X_add_one`. Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most
  propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py) ([`check.out`](certificate/check.out)): exact computation of
  a(0..240); equals the b-file ([`b193550.txt`](certificate/b193550.txt)); a(n) = Catalan(n) mod 4; B integral.
- Outside Lean: none. Not verified in Lean: agreement of `a` with the OEIS data (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry and its history list the claim as a conjecture with no proof. The
integrality of sqrt(1 + 4y) for integer y is standard (it is the Catalan generating function; see also
Heninger, Rains, Sloane, "On the integrality of n-th roots of generating functions", arXiv:math/0509316). The
reduction mod 4 to the Catalan continued fraction was not found in print. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
