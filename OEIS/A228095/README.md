# OEIS A228095, A225611, A226163: Sun's Legendre-symbol determinants vanish on residue classes

**Source.** Three conjectures of Zhi-Wei Sun (2013), with p = p_n the n-th prime and (·/p) the Legendre symbol:
- [A228095](https://oeis.org/A228095): det[((i^2 + 3ij + 3j^2)/p)]_{0<=i,j<=p-1} (Sun's [3,3]_p). "Conjecture: a(n) = 0
  if p_n == 5 (mod 6)." (revision #44 of Aug 25 2021)
- [A225611](https://oeis.org/A225611): det[((i^2 + 6ij + j^2)/p)]_{1<=i,j<=p-1} (Sun's (6,1)_p). "Conjecture: We have
  a(n) = 0 if p_n == 3 (mod 4)." (revision #52 of Aug 25 2021)
- [A226163](https://oeis.org/A226163): det[((i^2 - ((p-1)/2)! j)/p)]_{1<=i,j<=(p-1)/2}. "Conjecture: a(n) = 0 if and only if
  p_n == 3 (mod 4)." (revision #20 of Aug 19 2026, which links a proof)
(OEIS text checked 2026-11-06.)

**Result.**
- A228095: true. For p ≡ 5 (mod 6) the vector v_j = (j/p) is a nonzero kernel vector.
- A225611: true (known: Krachun, Petrov, Sun, Vsemirnov 2020); reproved here with the kernel vector v_j = (j/p).
- A226163: true (known: OEIS Open project, Adamczewski 2026, with a Lean proof); not redone here.

**Argument.** Write χ for the Legendre symbol on F_p.
- *A228095.* Row i of M v is Σ_y χ(i^2 + 3iy + 3y^2) χ(y). For i = 0 it is χ(3) Σ_y χ(y^3) = 0, because cubing permutes
  F_p when p ≡ 2 (mod 3). For i ≠ 0, put y = it: the row is χ(i^3) Σ_t χ(t + 3t^2 + 3t^3), and t = 1/s turns the
  summand into χ((s+1)^3 - 1) (the factor s^-4 is a square), so the sum is Σ_w χ(w^3 - 1) = Σ_z χ(z - 1) = 0.
- *A225611.* As above, row a of M v is χ(a^3) S with S = Σ_t χ(t^3 + 6t^2 + t). For p ≡ 3 (mod 4), -1 is a non-square,
  so every t ≠ 0 is u^2 or -u^2 (twice each) and 2S = (U - 1) - (T - 1) with U = Σ_u χ(u^4 + 6u^2 + 1),
  T = Σ_u χ(u^4 - 6u^2 + 1). Under u ↦ w = (1+u)/(1-u), w^4 - 6w^2 + 1 = -4(u^4 - 6u^2 + 1)/(1-u)^4 and
  w^4 + 6w^2 + 1 = 8(1 + u^4)/(1-u)^4. The first makes T odd under the involution apart from the end points u = 1,
  w = -1, giving T = -1. The second gives U = χ(2)(Σ_u χ(1 + u^4) - χ(2)) + χ(8), and Σ_u χ(1 + u^4) = -1 (from
  Σ_t χ(t^2 + 1) = -1 and Σ_t χ(t^3 + t) = 0), so U = -1. Hence S = 0. (S is minus the Frobenius trace of
  y^2 = x(x^2 + 6x + 1), which has CM by Z[2i]; the substitution is an explicit form of its supersingularity.)

**Evidence.**
- Lean (Mathlib): [`A228095_mathlib.lean`](A228095_mathlib.lean), namespace `OEIS_A228095`: `A228095_conj :
  p % 6 = 5 → (M p).det = 0` for the p × p matrix `M p i j = legendreSym p (i^2 + 3ij + 3j^2)` on `Fin p`.
  [`A225611_mathlib.lean`](A225611_mathlib.lean), namespace `OEIS_A225611`: `A225611_conj : p % 4 = 3 →
  (M p).det = 0` for the (p-1) × (p-1) matrix with indices 1..p-1. Both via `Matrix.exists_mulVec_eq_zero_iff` and
  the kernel vector above (`row_zero`, `key_sum`, `cube_bij`; `S_zero`, `sum_split`, `mobius_sum`, `T_sum`, `U_sum`,
  `sum_one_add_four`). Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext,
  Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): the kernel-vector identities for all primes p < 600 in the two
  classes, exact determinants for p < 40 (matching the entries' data), and T = U = -1, S = 0.
- Outside Lean: the reading p = p_n (the theorems are stated for every prime in the class); A226163 (cited).

**Review level.** `lean-proof` for A228095 and A225611; A226163 cited.

**Prior art.** Checked 2026-11-06.
- A225611: D. Krachun, F. Petrov, Z.-W. Sun, M. Vsemirnov, On some determinants involving Jacobi symbols, Finite
  Fields Appl. 64 (2020) 101672, prove (6,1)_p = [6,1]_p = 0 for p ≡ 3 (mod 4) (as stated in H.-L. Wu,
  arXiv:2012.05746). The OEIS entry does not mention it. No Lean proof found.
- A228095: H.-L. Wu, Elliptic curves over F_p and determinants of Legendre matrices (arXiv:2012.05746, 2021),
  Theorem 1.2(ii): [c,d]_p = 0 whenever p divides the central trinomial coefficient A_{c,d}(p); for c = d = 3 this
  holds for p ≡ 2 (mod 3) because the curve y^2 = x(3x^2 + 3x + 1) has trace 0 there. So the claim follows from Wu
  plus a standard supersingularity fact; the explicit kernel vector is ours.
- A226163: T. Adamczewski, OEIS Open, arXiv:2608.11941 (2026), Appendix A, with a Lean proof
  (github.com/epoch-research/LeanOpenProblems); google-deepmind/formal-conjectures marks it "research solved".
