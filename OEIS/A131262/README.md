# OEIS A131262: least k with A130654(k) = n equals sigma(2^n) phi(2^n)

**Source.** [A131262](https://oeis.org/A131262) (Adamchuk, 2007): a(n) = least index k with A130654(k) = n, where
A130654(k) is the exponent of 2 in A092505(k) = A002430(k)/A046990(k) (numerators of the Taylor coefficients of
tan x and of log(1/cos x)). Conjecture in the entry: a(n) = sigma(2^n) phi(2^n) = 2^(2n) - floor(2^n/2).
(OEIS text checked 2026-11-06; still marked conjecture; A130654 notes records at 1, 3, 14, 60, 248, 1008, ...
"strongly suggesting" the formula, Karttunen 2019.)

**Reading.** A130654(k) is read as the 2-adic valuation of A092505(k) (OEIS formula A130654 = A007814(A092505),
Karttunen). This equals the defining "m with 2^m = A092505(k)" whenever A092505(k) is a power of 2 (a separate
conjecture in A130654, true for k <= 1100 by certificate/check.py; not needed here).

**Result.** True: a(0) = 1 and a(n) = 2^(n-1)(2^(n+1) - 1) = sigma(2^n) phi(2^n) = 4^n - 2^(n-1) for n >= 1.

**Argument.** Let t_k = 2^(2k)(2^(2k) - 1)|B_(2k)|/(2k)! be the coefficient of x^(2k-1) in tan x, and
c_k = t_k/(2k) that of x^(2k) in log(1/cos x).
1. v2(B_(2k)) = -1 (von Staudt-Clausen at 2), 2^(2k) - 1 is odd, and v2((2k)!) = 2k - s2(k) (Legendre, s2 = binary
   digit sum). So v2(t_k) = s2(k) - 1 >= 0 and v2(c_k) = s2(k) - 2 - v2(k).
2. For a rational q, v2(numerator q) = max(v2 q, 0). Hence A130654(k) = v2(num t_k) - v2(num c_k)
   = min(s2(k) - 1, 1 + v2(k)).
3. A130654(k) >= n >= 1 forces 2^(n-1) | k and s2(k) >= n + 1. Write k = 2^(n-1) m; s2(m) = s2(k) >= n+1 and
   m + 1 >= 2^(s2 m), so k >= 2^(n-1)(2^(n+1) - 1). At k = 2^(n-1)(2^(n+1) - 1): v2 = n - 1, s2 = n + 1, value n.

**Evidence.**
- Lean (Mathlib): [`A131262_mathlib.lean`](A131262_mathlib.lean), importing `OpenProblemsLib.BernoulliDen`
  (`bernoulli_den_mod4`). Main theorems `A131262_isLeast` (n >= 1: IsLeast {k >= 1 : A130654 k = n}
  (2^(n-1)(2^(n+1)-1))), `A131262_zero`, `kstar_sigma_phi` (= sigma(2^n) phi(2^n) = 2^(2n) - 2^n/2), via
  `A130654_eq` (step 2), `tan_val`, `bern_val`, `num_val`, `pow_s2_le`. Check `tools/leancheck-mathlib.sh`: OK, no
  warnings, axioms propext, Classical.choice, Quot.sound.
- [`certificate/check.py`](certificate/check.py): tan coefficients from the zigzag numbers for k <= 1100; the min
  formula holds, every A092505(k) is a power of 2, and the least indices are 1, 3, 14, 60, 248, 1008.
- Outside Lean: the classical identity "Taylor coefficient of x^(2k-1) in tan x = 2^(2k)(2^(2k)-1)|B_(2k)|/(2k)!"
  (Abramowitz-Stegun 4.3.67); log(1/cos x) is taken as the series with derivative tan x and constant term 0.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: entries A131262, A130654, A092505 (no proof); web search (no hit);
google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs trees (no file). Ingredients classical
(von Staudt-Clausen, Legendre); the derivation appears new.
