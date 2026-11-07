# OEIS A218622: A183161(n) mod 4 never equals 3

**Source.** [A218622](https://oeis.org/A218622) (Hanna, 2012): a(n) = A183161(n) mod 4, where A183161 has a(0) = 1
and self-convolution A183160(n) = sum_{k=0..n} C(n+k, n-k) C(2n-k, k). Comment: "Conjecture: a(n) never equals 3."
(OEIS text checked 2026-11-07 from the cached entry.)

**Result.** True; this is the conjecture of [A183161](../A183161/README.md). A218622 is the output of a six-state
automaton on the binary digits of n (least significant first): transitions on 0: (0, 0, 3, 4, 4, 5), on 1:
(1, 2, 2, 5, 3, 5), outputs (1, 1, 2, 2, 2, 0).

**Argument.** See [OEIS/A183161](../A183161/README.md): Lagrange inversion for x = t(1-t)^2 gives
A183161(n) = [t^n] S(t) (1-t)^(-2n-1) with S = sqrt((1-3t)/(1+t)); S ≡ 1 + 2W (mod 4) for a lacunary W; the
Rowland-Yassawi Cartier operators on the resulting bivariate rational function over ℤ/4 close on six states.

**Evidence.**
- Lean: [`A218622_mathlib.lean`](A218622_mathlib.lean): `A183161_spec`, `A183161_unique` (the library's integer
  sequence `OpenProblemsLib.HannaMod4.A183161` has value 1 at 0 and self-convolution A183160, and it is the only one;
  integrality via Catalan numbers, see [OEIS/A183161](../A183161/README.md)), `A218622_ne_three` (A218622(n) =
  A183161(n) mod 4 ≠ 3) and `A218622_ne_three_of_conv` (any integer sequence with b(0) = 1 and self-convolution A183160
  has b(n) mod 4 ≠ 3), via `OpenProblemsLib.HannaMod4`. Axioms: propext, Classical.choice, Quot.sound.
- Numerics: [OEIS/A183161/certificate/gf_check.py](../A183161/certificate/gf_check.py) (n ≤ 300);
  [OEIS/A183161/certificate/rootseq_check.py](../A183161/certificate/rootseq_check.py) (the Lean definition mod 4 agrees
  with the 60 cached terms).
- Outside Lean: none. The printed OEIS terms are not used by the proof.

**Review level.** `lean-proof`.

**Prior art.** As for A183161 (checked 2026-11-07): no proof or formalisation found.
