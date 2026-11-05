# OEIS A118990: A118990(n) = 2^n A086906(n-1)

**Source.** OEIS [A118990](https://oeis.org/A118990), number of symmetric singular n X n
(+1,-1) matrices over the reals (0, 4, 32, 512, 15872, ...; offset 1), and OEIS
[A086906](https://oeis.org/A086906), number of symmetric singular n X n (0,1) matrices over
the reals (1, 4, 32, 496, 14172, ...; offset 1). Each entry lists the other under Cf.; neither
states a formula between them (both entries read 2026-11-05). The idea comes from OpenAI
manuscript family 239, "The sharp exponential rate of singularity for symmetric Bernoulli
matrices" (OpenAI, October 3, 2026), Lemma 2.1: for n >= 2 a uniform symmetric sign matrix
A_n and a uniform symmetric 0/1 matrix B_(n-1) are singular with the same probability.

**Result.** For n >= 2, A118990(n) = 2^n A086906(n-1). Proved in Lean (all n).

**Argument.** Fix n >= 0 and write matrices of size n+1 with indices 0..n.
Given a sign vector s (length n+1) and a symmetric 0/1 matrix B of size n, put
e = (1, s_1, ..., s_n), let N be the matrix with first row and first column all 1 and
N_ab = 1 - 2 B_ab for a, b >= 1, and set M = s_0 diag(e) N diag(e), that is
M_00 = s_0, M_0b = M_b0 = s_0 s_b, M_ab = s_0 s_a s_b (1 - 2 B_ab).
M is symmetric with entries +1/-1.
Conversely, a symmetric sign matrix M gives back s_0 = M_00, s_k = M_00 M_0k and
B_ab = (1 - M_00 M_0a M_0b M_ab)/2 in {0, 1}, and the two maps are inverse to each other
(this uses s_i^2 = 1 and M_0k = M_k0). So (s, B) <-> M is a bijection between
{+1,-1}^(n+1) x {symmetric 0/1 matrices of size n} and symmetric sign matrices of size n+1.
The case M_00 = -1 needs no special treatment: it is absorbed in s_0 = -1.
Determinant: det M = s_0^(n+1) (prod e_i)^2 det N, and subtracting row 0 from every other row
of N leaves first column (1, 0, ..., 0) and lower block -2B, so det N = (-2)^n det B.
Hence M is singular iff B is, and the singular sign matrices number 2^(n+1) times the
singular 0/1 matrices. With n+1 = the OEIS index this is A118990(n) = 2^n A086906(n-1).
The count form of OpenAI's Lemma 2.1 is the same statement: multiplying the equal
probabilities by 2^(n(n+1)/2) and 2^((n-1)n/2) gives the factor 2^n.

**Evidence.**
- `A118990_mathlib.lean` (Mathlib), theorem `A118990_eq (n : ℕ) :
  (A118990_pm (n + 1)).card = 2 ^ (n + 1) * (A118990_zo n).card`, where `A118990_pm m` /
  `A118990_zo m` are the Finsets of m x m integer matrices with entries in {1, -1} / {0, 1},
  symmetric, with `det = 0`. Helper `A118990_det_norm`: det N = (-2)^n det B. The bijection
  is `A118990_fwd` / `A118990_bwd` with `Finset.card_nbij'`. Axioms: propext,
  Classical.choice, Quot.sound; no sorry, no native_decide; zero warnings
  (`tools/leancheck-mathlib.sh`, 2026-11-05).
- `certificate/check.py`: brute-force counts for n <= 5 (both sequences) agree with the OEIS
  terms, and the identity holds for all listed OEIS terms n = 2..10.
- Outside Lean: the identification of the Finset cards with the OEIS sequences (definitions
  match the OEIS names; numeric agreement n <= 5 by check.py). No small term is evaluated in
  Lean (the Finsets use classical decidability).

**Review level.** lean-proof. Re-derived independently of the preprint (explicit bijection
rather than its probabilistic conditioning), and checked numerically.

**Prior art (2026-11-05).** OEIS A118990 and A086906: formula not stated (only Cf. links and
complement formulas via A118992 and A086899). OpenAI family 239 (preprint dated 2026-10-03,
Lemma 2.1) states the equivalent probability identity with a one-paragraph proof (diagonal
congruence plus Schur complement); the identity is therefore immediate from that source. The
OpenAI Lean collection (`lean/` in openai/math) has no doc or formalisation for family 239
(no `lean/docs/239.md`, no entry in `formalization.yaml`), so there is no earlier Lean proof
there. google-deepmind/formal-conjectures has no `FormalConjectures/OEIS/118990.lean` or
`86906.lean` (HTTP 404, 2026-11-05).
