# OEIS A037097, A037096, A036284: (x+1)- and (x^3+1)-power factors of periodic binary columns

**Source.** Antti Karttunen's entries (OEIS text, CC BY-SA 4.0, checked 2026-11-06):
- [A037097](https://oeis.org/A037097): periodic vertical binary vectors of powers of 3, starting from bit column 2
  (halved), a(n) = Sum_{k=0..2^(n-1)-1} (floor(3^k/2^n) mod 2) 2^k. Comment, as corrected by Qiyuan Gu (Jul 24 2026):
  for n >= 3, a(n) as a GF(2)[X] polynomial is divisible by (x+1)^A000225(n-2). The scan record quotes the older
  exponent A000225(n-1).
- [A037096](https://oeis.org/A037096): the same over k < 2^n; conjecture: (x+1)^A055010(n-1) divides a(n), n >= 3.
- [A036284](https://oeis.org/A036284): periodic vertical binary vectors of Fibonacci numbers, k < 3*2^n; conjecture:
  (x^3+1)^A000225(n-1) divides a(n) for n >= 1; "Conjecture 2: there is also one extra (x^1 + 1) factor present".

**Reading.** "a(n) considered as a GF(2)[X]-polynomial": binary digit k of a(n) is the coefficient of x^k, so
a(n) is Sum_k bit_n(f(k)) x^k with f(k) = 3^k or F_k. A000225(j) = 2^j - 1, A055010(n-1) = 3*2^(n-2) - 1.

**Result.**
- A037097: the corrected statement is true, with exact exponent 2^(n-2) - 1. The older exponent 2^(n-1) - 1 (the
  scan record's version) is false: a(3) = 12 = x^2 + x^3 = x^2 (x+1) and a(4) = 120 = x^3 (x+1)^3.
- A037096: true.
- A036284: both conjectures true.

**Argument.** Bit flips. For n >= 3, 3^(2^(n-2)) = 1 + 2^n u with u odd (induction by squaring), so
3^(k+M) = 3^k + 2^n (3^k u) and bit n of 3^k flips when k grows by M = 2^(n-2). For the Fibonacci numbers and
n >= 2, L = 3*2^(n-1) gives F_L = 2^(n+1) * odd and F_(L-1) = 1 + 2^n (mod 2^(n+1)) (induction with
F_2L = F_L (2F_(L+1) - F_L) and F_(2L-1) = F_L^2 + F_(L-1)^2), so F_(k+L) = F_k F_(L-1) + F_(k+1) F_L flips bit n
exactly when F_k is odd, i.e. 3 does not divide k.
Polynomials. If q_(k+M) = q_k + c_k then Sum_{k<2M} q_k x^k = A (1 + x^M) + x^M Sum_{k<M} c_k x^k with
A = Sum_{k<M} q_k x^k. Over GF(2), 1 + x^(2^j) = (1+x)^(2^j) and Sum_{k<2^j} y^k = (1+y)^(2^j - 1).
- A037097 (c = 1): a(n) = A (1+x)^M + x^M (1+x)^(M-1) = (1+x)^(M-1) (A(1+x) + x^M); the cofactor is 1 at x = 1.
- A037096: bit n has period 2^(n-1), so A037096(n) = A037097(n) (1+x)^(2^(n-1)), exponent 3*2^(n-2) - 1.
- A036284 (c_k = 1 iff 3 does not divide k, N = 2^(n-1)): Sum_{k<L} c_k x^k = (x + x^2)(1+x^3)^(N-1), so
  a(n) = A (1+x^3)^N + x^(L+1)(1+x)(1+x^3)^(N-1) = (1+x^3)^(N-1) (1+x) (A(1+x+x^2) + x^(L+1)).
  n = 1 directly: a(1) = x^3 + x^4.

**Evidence.**
- Lean (Mathlib): [`A037097_mathlib.lean`](A037097_mathlib.lean). `A037097_dvd : 3 ≤ n → ∃ R, A037097poly n =
  (X+1)^(2^(n-2)-1) * R ∧ R.eval 1 = 1`; `A037096_dvd : 3 ≤ n → (X+1)^(3*2^(n-2)-1) ∣ A037096poly n`;
  `A036284_dvd : 1 ≤ n → (X^3+1)^(2^(n-1)-1) * (X+1) ∣ A036284poly n`; polynomials over `ZMod 2` with coefficients
  `floor(f k / 2^n)` cast to `ZMod 2`. `tools/leancheck-mathlib.sh`: OK, no warnings; axioms at most propext,
  Classical.choice, Quot.sound.
- [`certificate/check.py`](certificate/check.py): the flip lemmas and the exact (x+1)- and (x^3+1)-adic valuations
  for n <= 11 (powers of 3) and n <= 9 (Fibonacci). For A036284 the x+1 exponent is in fact 2^(n-1) for n >= 4.
- `A037097_old_exponent_false`: the older exponent fails at n = 3 (a(3) = x^2 (x+1)).
- Outside Lean: the reading.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entries state the divisibilities as conjectures (A037097's exponent corrected
by Q. Gu in Jul 2026 without a proof note). Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
The bit-flip facts are standard 2-adic properties of 3^(2^j) and of the Pisano period mod 2^n.
