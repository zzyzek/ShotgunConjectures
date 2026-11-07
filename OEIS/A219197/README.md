# OEIS A219197: the square root of the A199033 g.f. has no coefficient = 3 (mod 4)

**Source.** [A219197](https://oeis.org/A219197) (Hanna, 2012): a = 1, 2, 9, 46, 253, ..., the self-convolution square
root of A199033(n) = sum_k C(n+k+1, n-k) C(2n-k+1, k). G.f. formula in the entry: A = G/sqrt(1 - 2xG^2 - 3x^2G^4),
G = 1 + xG^3. Comment: "Conjecture: a(n) is never congruent to 3 modulo 4." (OEIS text checked 2026-11-06.)

**Result.** True. Moreover a(n) is odd iff n is even and n AND 2n = 0 (no two adjacent 1-bits), and then a(n) = 1
(mod 4).

**Argument.**
1. *Lagrange form.* Put t = xG^2; then G = 1/(1-t) and x = t(1-t)^2. The entry's g.f. becomes
   A = (1-t)^(-1) (1-2t-3t^2)^(-1/2), and Lagrange inversion ([x^n] H = [t^n] H(t) phi^n (1 - t phi'/phi),
   phi = (1-t)^(-2)) gives a(n) = [t^n] S(t) (1-t)^(-2n-2), S = sqrt((1-3t)/(1+t)).
2. *S mod 4.* (1-3t)/(1+t) = 1 - 4u with u = t/(1+t), so S = sqrt(1-4u) = 1 - 2 sum_{k>=1} Cat(k-1) u^k. Cat(k-1) is
   odd iff k is a power of 2, and u^(2^j) = t^(2^j)/(1+t^(2^j)) (mod 2). Hence S = 1 + 2W (mod 4) with
   W = sum_m (v2(m) + 1) t^m (mod 2), and
   a(n) = C(3n+1, n) + 2 E(n) (mod 4),  E(n) = sum_{1<=m<=n, v2(m) even} C(3n+1-m, n-m).
3. *Parity.* C(3n+1, n) = C(n + (2n+1), n) is odd iff adding n and 2n+1 has no carry, i.e. n even and n AND 2n = 0.
   By Lucas, C(3n+1-m, n-m) = C(k + (2n+1), k) with k = n-m is odd iff k AND (2n+1) = 0, so
   E(n) = #{0 <= k < n : k AND (2n+1) = 0, v2(n-k) even} (mod 2).
4. *C(3n+1, n) mod 4.* From (1+t)^(2x) = (1+t^2+2t)^x = (1+t^2)^x + 2xt(1+t^2)^(x-1) (mod 4), C(2x, 2y) = C(x, y)
   (mod 4); with C(2x+1, 2y) = C(2x, 2y)(2x+1)/(2x-2y+1) and C(2x+1, 2y+1) = C(2x, 2y)(2x+1)/(2y+1) and
   2z+1 = (-1)^z (mod 4), a carry-free C(a, b) is (-1)^N (mod 4), N = #{i : a_(i+1) = a_i = 1, b_(i+1) != b_i}. For
   a = 3n+1, b = n (n even, no adjacent 1-bits) this is N(n) = popcount(n) + #{i >= 0 : n_(i+1) = 1, (2n+1)_i = 1}.
5. *E = N (mod 2).* Write n = 2^e + n' with n' < 2^(e-1) (top bit e, next bit e2 <= e-2 if n' > 0). The k >= 2^e
   are 2^e + k'' with k'' counted by E(n'). The k < 2^e range over the span of the free positions F = {1..e-1}
   minus {e_j + 1 : j >= 2}; k = n' gives v2 = e, and for k != n', v2(n-k) = v2(n'-k) = v exactly for 2^|F cap (v, e-1]|
   values of k when v is in F (none otherwise). Mod 2 only v = max F survives, so this part is
   [max F even] + [e even]: 1 if e >= 2 and e2 != e-2 (or n' = 0), 0 if e2 = e-2 or e = 1. The same top-bit step
   changes N by 1 + [e2 = e-2] (by 1 + [e = 1] when n' = 0). Induction from E(0) = N(0) = 0 gives E = N (mod 2).
6. Hence for odd a(n): a(n) = (-1)^N + 2N = 1 (mod 4); otherwise a(n) is even. So a(n) is never 3 mod 4.

**Lean proof (second argument).** The same Lagrange step (1) holds in the form [x^n] F = [t^n] F(t(1-t)^2) (1-3t)
(1-t)^(-2n-1) for every F, and A199033(n) = [t^n] (1-t)^(-2n-3)/(1+t) by the Fibonacci-polynomial identity
(1+t) sum_k C(N-k, k) t^k (1-t)^(N-2k) = 1 - (-t)^(N+1) with N = 2n+1. So a(n) = [t^n] S (1-t)^(-2n-2) with
S = sqrt((1-3t)/(1+t)) follows from the definition (no g.f. formula assumed), S ≡ 1 + 2W (mod 4), and a(n) mod 4 is the
output of the six-state automaton of [A183161](../A183161/README.md) started in state 1 (Rowland-Yassawi Cartier
operators over ℤ/4); outputs 0, 1, 2.

**Evidence.**
- Lean: [`A219197_mathlib.lean`](A219197_mathlib.lean). `A219197` is defined in the library as the integer sequence
  [t^n] R(t) (1-3t) (1-t)^(-2n-2), R = 1/sqrt((1-3t)(1+t)) (integer coefficients via the Catalan series, see
  [OEIS/A183161](../A183161/README.md)). Theorems: `A219197_spec` (A219197(0) = 1 and its self-convolution is A199033),
  `A219197_unique` (the only integer sequence with these properties), `A219197_ne_three` (A219197(n) mod 4 ≠ 3),
  `A219197_def_mod4` (any integer sequence with a(0) = 1 and self-convolution A199033 has a(n) mod 4 ≠ 3) and
  `A219197_mod4` (from Hanna's g.f.), via `OpenProblemsLib.HannaMod4` and `OpenProblemsLib.AutomaticMod`. Axioms:
  propext, Classical.choice, Quot.sound.
- [`certificate/gf_check.py`](certificate/gf_check.py): g.f. formula, square root, "never 3" and the automaton for n ≤ 300.
- [`certificate/f.py`](certificate/f.py), [`certificate/g.py`](certificate/g.py), [`certificate/h.py`](certificate/h.py),
  [`certificate/m.gp`](certificate/m.gp): numerical checks of the first (paper) argument, steps 1-5.
- [OEIS/A183161/certificate/rootseq_check.py](../A183161/certificate/rootseq_check.py): the Lean definition agrees with
  the 24 cached OEIS terms.
- Outside Lean: none. The first (paper) argument is an independent second proof and is not formalised; the printed
  OEIS terms are not used by the proof.

**Review level.** `lean-proof` (the paper argument above and the Lean route are independent).

**Prior art.** Checked 2026-11-06 and 2026-11-07: entry (unannotated), not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs. No proof found.
