# OEIS A103990 / A103991: sqrt(pi) I(n,0) = (2/3)(n^3 - n^2 + 2n + 1)/(2n + 1)

**Source.** [A103990](https://oeis.org/A103990) (Eric W. Weisstein, Feb 23 2005): "Reduced numerators of the
hypercube line-picking integrand sqrt(Pi)*I(n,0)"; [A103991](https://oeis.org/A103991): the denominators. Comment in
A103990: "Conjecture: Let b(n) be A103991(n), then a(n)/b(n) = (2/3)*(n^3-n^2+2*n+1)/(2*n+1). - _Gerald McGarvey_,
Aug 11 2009". Data: 20 terms. The integrand comes from MathWorld's
[Hypercube Line Picking](https://mathworld.wolfram.com/HypercubeLinePicking.html), which credits M. Trott (personal
communication, 2005) with an algorithm that reduces the mean distance Delta(n) in the unit n-cube to
Delta(n) = Int_0^oo I_n(x) dx and prints I_1, ..., I_4. (OEIS text, CC BY-SA 4.0, revision #10 of Feb 16 2025;
MathWorld checked 2026-11-06.)

**Reading.** Trott's algorithm is not published. We read I_n as follows. With d(u) = Int_0^1 Int_0^1
e^{-u^2 (x-y)^2} dx dy = (e^{-u^2} - 1 + sqrt(pi) u erf u)/u^2 (MathWorld Eq. 10), Delta(n) =
(1/sqrt(pi)) Int_0^oo (1 - d(u)^n)/u^2 du (Eq. 8 with s = 1). I_n is the unique element of the span of
e^{-k x^2} erf(x)^l / x^(l mod 2) (k >= 1) that differs from (1/sqrt(pi)) (1 - d^n)/u^2 by a derivative of a
function of the same kind (integration by parts; the allowed functions are u^b e^{-k u^2} erf(u)^l with k >= 1, or
k = 0 and b != 0). This reading reproduces MathWorld's four integrands I_1, ..., I_4 term by term and all 20 data
terms of A103990/A103991 (certificate/check_trott.py).

**Result.** True under this reading: sqrt(pi) I(n,0) = (2/3)(n^3 - n^2 + 2n + 1)/(2n + 1) for every n >= 1.
Equivalently sqrt(pi) I(n,0) = (4n^2 - 6n + 11)/12 - 1/(4(2n+1)).

**Argument.** Write t = u^2, X = e^{-u^2}, W = sqrt(pi) erf(u)/u (so d = W - (1 - X)/t) and use monomials
t^j X^k W^l.
1. *Relations.* For h = u t^j X^k W^l, D h = (1 + 2j - l) t^j X^k W^l - 2k t^(j+1) X^k W^l + 2l t^j X^(k+1) W^(l-1);
   h is allowed unless k = 0 and l = 2j + 1. The basis is X^(g-l) W^l t^(floor(l/2)) (0 <= l < g), with value
   at 0 equal to 1 (l = 0), 2 (l = 1), 0 (l >= 2).
2. *The value functional.* For fixed (k >= 1, l), the relation at j links V(j), V(j+1) and V(j, k+1, l-1).
   Fixing V on the basis (at j0 = floor(l/2)) and solving upwards and downwards in j uses every relation
   exactly once, so this V kills all relations; for k = 0 the relation defines V(j, 0, l). Hence the value at 0
   of the canonical form of f is V(f), canonical forms are unique (the same construction with other anchor
   values separates the basis), and sqrt(pi) I(n,0) = V((1 - d^n)/t). Below the anchor, V(-tau, k, l) =: Vn
   obeys (1 - 2tau - l) Vn(tau, k, l) = 2k Vn(tau-1, k, l) - 2l Vn(tau, k+1, l-1), Vn(tau, k, 0) =
   (-2)^tau k^tau/(2tau-1)!!, Vn(0, k, l) = 2^l l.
3. *Polynomiality.* By that recursion Vn(tau, ., l) is a polynomial in k of degree <= tau. Expanding
   (1 - d^n)/t = t^-1 - Sum C(n,i) C(i,m) (-1)^(i+m) t^-(i+1) X^m W^(n-i), the sum over m is an i-th forward
   difference of a polynomial of degree i+1, so only its two top coefficients survive:
   sqrt(pi) I(n,0) = -Sum_i C(n,i) q(i, n-i), with q(tau,l) = Delta^tau Vn(tau+1, ., l)(0) and
   a(tau,l) = Delta^tau Vn(tau, ., l)(0) obeying first-order recursions in (tau, l).
4. *Closed forms.* With I(alpha,beta) = Int_0^1 r^(alpha+beta) (r-2)^alpha dr:
   a(tau,l) = (-1)^tau l 2^l - 2^(l+1) tau I(tau-1, l) (tau >= 1), a(0,l) = l 2^l (l >= 1), a(0,0) = 1, and
   q(tau,l) = (-1)^tau 2^l (-l(2l + 3tau)/6) + 2^l ((l^2 - 2l tau - 5l - 3tau^2 - 3tau)/3) I(tau,l).
   They satisfy the recursions by two integration-by-parts relations for I (found from the generating functions
   G = 1 + 2y e^{-x+2y} - 2x e^{-x+2y} J and K, J = Int_0^1 e^{x s^2 - 2ys} ds, which solve the first-order PDEs
   of the recursions; certificate/pde_check.py, certificate/series_check.py).
5. *Diagonal sum.* Sum_i C(n,i) 2^(n-i) I(i, n-i) w(i) = Int_0^1 r^n Sum_i C(n,i) w(i) (r-2)^i 2^(n-i) dr, and the
   binomial moments give -Sum_i C(n,i) q(i,n-i) = (n^2 - 3n + 2)/3 + n(n+1)/(2n+1)
   = (2/3)(n^3 - n^2 + 2n + 1)/(2n+1).

**Evidence.**
- Lean (Mathlib): [`A103990_mathlib.lean`](A103990_mathlib.lean). Formal model: monomials t^j X^k W^l
  (`Mon = ℤ × ℕ × ℕ`), `Fn n` = (1 - d^n)/t, `rel j k l` = D(u t^j X^k W^l), `Rels` the allowed ones, basis
  t^(l/2) X^k W^l (k ≥ 1) with value `anc l` at u = 0. Main theorem `A103990_canonical`: for n ≥ 1, any
  combination of basis elements congruent to `Fn n` modulo `Rels` has value (2/3)(n^3 - n^2 + 2n + 1)/(2n + 1)
  at 0. Route: `V`, `G_rel`, `V_rel`, `VL_rel`, `V_anchor` (Argument 1-2), `Vn_eq`, `VL_Fn`, `S_eq`, `T_zero`,
  `a_succ`, `q_succ` (Argument 2-3), `I0`, `I1`, `Jrel`, `Krel`, `a_eq`, `q_eq` (Argument 4, with `ι` =
  Int_0^1 on Q[X] and `ι_deriv`), `B0`-`B2`, `diag0`, `diag1`, `diag_qE`, `A103990_main` (Argument 5).
  Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext, Classical.choice,
  Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/canon.py`](certificate/canon.py), [`certificate/check_trott.py`](certificate/check_trott.py): the
  integration-by-parts reduction; it reproduces MathWorld's I_1..I_4 exactly and the 20 terms of A103990/A103991,
  and gives the formula for n <= 25.
- [`certificate/vn.py`](certificate/vn.py), [`certificate/ab_check.py`](certificate/ab_check.py),
  [`certificate/closed.py`](certificate/closed.py): the recursion, polynomiality, top coefficients and closed
  forms against the reduction; [`certificate/pde_check.py`](certificate/pde_check.py),
  [`certificate/series_check.py`](certificate/series_check.py): the generating functions that suggested the
  closed forms (sympy; not needed for the Lean proof).
- Outside Lean: the reading of Trott's unpublished integrand, i.e. the dictionary between the functions
  (e^{-u^2}, erf, powers of u) and the formal monomials, the value at 0 of the basis functions, and that
  Trott's I_n is a canonical combination in this sense (it is for n <= 4 by MathWorld's formulas, and the
  reduction in certificate/canon.py produces one for every n tried).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entries and their histories (A103990 to #10, A103991 to #25) keep the
conjecture; A103991 also has an empirical g.f. (Colin Barker) and a conjectured trisection (Ralf Stephan, 2010),
which the formula implies for the reduced denominators only after reduction, not treated here. MathWorld gives
I_1..I_4 and the first values but no general formula. Not in google-deepmind/formal-conjectures (no file for
103990) or otoi-lab/oeis-lean-proofs. A web search found no proof.
