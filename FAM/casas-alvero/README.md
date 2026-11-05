# Casas-Alvero conjecture in degrees 2 to 6, in Lean (FAM-casas-alvero)

Famous-problem round 2, 2026-11-05. The conjecture is not settled here.

## Source

Casas-Alvero (2001): over a field of characteristic 0, a monic polynomial P of degree d that
shares a root (equivalently a nontrivial factor) with each of its derivatives P', …, P^(d−1)
is (X − α)^d. Wikipedia "Casas-Alvero conjecture"; formal-conjectures
`FormalConjectures/Paper/CasasAlvero.lean` (fetched 2026-11-05): `casas_alvero_conjecture`
tagged `research open`; `prime_power` and `double_prime_power` tagged `research solved` with
`sorry`; only `positive_char_counterexample` has a `formal_proof` link (AlphaProof). The FC file
states the conjecture with Hasse derivatives and coprimality (`HasCasasAlveroProp`); Hasse and
ordinary derivatives differ by the unit i! in characteristic 0.

## Literature status (checked 2026-11-05)

| degrees | status | source |
|---|---|---|
| p^k, 2p^k | proved | Graf v. Bothmer–Labs–Schicho–van de Woestijne, J. Algebra 2007 (arXiv math/0605090); Draisma–de Jong (EMS Newsletter 2011) |
| 5p^e | proved | Chellali–Salinier, arXiv:1211.2059 (2012) |
| 12 | proved (computer-assisted) | Castryck–Laterveer–Ounaïes, Math. Comp. 83 (2014) 3017–3037 (arXiv:1208.5404) |
| d ≤ 8 | listed as proved | FC file docstring |
| 20 | smallest degree open in refereed literature | Wikipedia (after the degree-12 result) |
| all d | proof claimed, not refereed | Ghosh, arXiv:2501.09272 (v1 16 Jan 2025, v2 21 Mar 2026 "Major revisions"); no erratum or refutation found |

So the smallest degree not covered by the refereed literature is 20; that is far outside the
method used here (see Obstacles).

## Result (Lean)

`casas_alvero_mathlib.lean` (degrees 2–5, 28 theorems, about 15 s) and `casas_alvero6_mathlib.lean`
(degree 6, 59 theorems, 794 KB, 171 s wall in one 6 GB slot). Each file is self-contained.

| Lean name | Statement in words |
|---|---|
| `casas_alvero_deg_d` (d = 2, 3, 4, 5, 6) | for any field `K` of characteristic 0 and monic `P : K[X]` of degree `d` with `HasCasasAlveroProp P` (not coprime to any Hasse derivative of order `< d`), `P = (X − C α)^d` for some `α : K` (FC statement shape, degree fixed) |
| `casas_alvero_root_deg_d` | the same with the root hypothesis (`P` and its `i`-th Hasse derivative have a common root in `K`) |
| `core<d>` | the normalised algebra: if `Q = x^d + Σ_{j=1}^{d−2} b_j x^j` has a root `x_i` in common with `Q^(i)/i!` for each `1 ≤ i ≤ d − 2`, then every `b_j = 0` |
| `core<d>_r<i>`, `core<d>_t<j>`, `core<d>_c<mask>_<j>`, `core<d>_case<mask>` | the individual certificate identities (one declaration each) |
| `of_algClosure` | coprime version over `K` from the root version over `AlgebraicClosure K` (FC's `casas_alvero_iffᵣ` argument, one degree) |
| `eval_hasseDeriv_sum`, `eq_X_sub_C_pow` | evaluation of Hasse derivatives through coefficients; a monic polynomial with the binomial coefficients of `(X − a)^d` equals `(X − C a)^d` |

`HasCasasAlveroProp`, `HasCasasAlveroPropR` and the lemmas `HasCasasAlveroProp.map_iff`,
`hasCasasAlveroProp_iffR` are copied from formal-conjectures (Apache 2.0).

Axioms (`tools/leancheck-mathlib.sh`, 2026-11-05): propext, Classical.choice, Quot.sound for
every theorem (the certificate lemmas use only propext, Quot.sound). No sorry, no native_decide,
zero warnings. The `set_option maxHeartbeats 0` in `casas_alvero6_mathlib.lean` is on the large
certificate declarations only; the 900 s / 6 GB limits of the check script still apply.

## Argument

1. Pass to the algebraic closure (coprime ⇔ common root there; the root α found there equals
   −nextCoeff(P)/d, which lies in K).
2. Let a be the common root of P and its (d−1)-th Hasse derivative (which is d·X + c_{d−1}, so
   a = −c_{d−1}/d), and write P(X) = Q(X − a) with Taylor coefficients b_j. Then b_{d−1} = 0 and
   b_0 = P(a) = 0, and the shared roots x_i − a of the other derivatives satisfy the normalised
   equations. These translation identities are `linear_combination`s checked by `ring`.
3. `core<d>`: eliminate each shared root x_i by an explicit resultant identity
   N_i·Res_x(Q, H_i) = U·Q(x_i) + V·H_i(x_i). For d ≤ 5 an identity N·b_j^e = Σ g_i Res_i
   gives b_j = 0 (exponents e: d = 4: 6, 7; d = 5: 10, 13, 19). For d = 6, Res_i = c·b_i^{m}·S_i,
   and the proof splits on b_i = 0 or S_i = 0 (16 cases); each case has its own identity
   N·b_j^e ∈ (b_i, S_k) (largest e = 25, largest denominator 450 digits).
4. With all b_j = 0, P = (X − a)^d coefficient by coefficient.

All cofactors were found by exact weighted-homogeneous linear algebra (Macaulay matrices, PARI/gp
`matinverseimage` over Q after a mod-p feasibility test); Lean re-checks every identity with
`ring`, so nothing about the search is trusted.

## Evidence and rebuild

* `certificate/gen_lean.py`: certificate search (stage 1 resultant cofactors, stage 2
  b_j^e membership; `solve_member`, `gp_solve`), monolithic `core<d>` for d ≤ 5.
* `certificate/split_core.py`: splits the d ≤ 5 core into one declaration per identity.
* `certificate/gen_cases.py`: the case-split core for d ≥ 6.
* `certificate/gen_degree.py`, `certificate/header.lean`: assemble a file. Rebuild (in
  `certificate/`, needs PARI/gp): `python3 gen_degree.py 2 3 4 5 > ../casas_alvero_mathlib.lean`
  (2 s), `python3 gen_degree.py 6 > ../casas_alvero6_mathlib.lean` (45 s).
* `certificate/cases_probe.py d`: certificate sizes of the case-split route for degree d.

Outside Lean: nothing for the stated theorems (the generator is untrusted and not needed).

## Obstacles

* **Certificate size, unsplit route (d = 6).** Stage 2 without case split needs b_4^36 and
  970-digit coefficients; the certificate is 2.5 MB, one identity (736 KB) checks alone in 72 s,
  all four together exceed 6 GB (exit 137). Splitting into one declaration per identity did not
  help. The case split on the factorisation Res_i = c·b_i^m·S_i cut it to 0.73 MB and checks.
* **d = 7 and beyond.** With the case split, the main case (all S_i = 0) gives a Macaulay system
  of 1932 × 2572 for b_1^e that is solvable mod p, but the exact rational solve in PARI/gp exceeds
  a 1.6 GB stack under the 2 GB process cap (`certificate/cases_probe.py 7`). A multimodular solve
  with rational reconstruction, or a tracked Gröbner basis (many small identities instead of one
  large one), is the next step; the Lean cost is then unknown (d = 6 already has 450-digit
  denominators and about 1 MB of ring certificate per file is the observed limit). The route is degree-by-degree; d = 20 (the
  first degree not covered in the refereed literature) has 18 coefficients and is out of reach.
  A uniform proof would need the p-adic/valuation argument of Graf v. Bothmer et al. (for
  d = p^k), which rests on the finiteness of the Casas-Alvero scheme, or Ghosh's Koszul-homology
  argument; neither is in Mathlib.

## Prior art (2026-11-05)

formal-conjectures CasasAlvero.lean (no formal proof of any degree; only the char-p
counterexample); web search for a Lean or other formal proof of any degree: none found. The
triage note "Lean for d ≤ 4" in `candidates.jsonl` was a target, not an existing result.

## New or known

Known mathematics (degrees 2–6 are covered by the p^k and 2p^k theorems and older computer
checks). New as far as found: machine-checked proofs, in the formal-conjectures statement shape,
for degrees 2, 3, 4, 5 and 6, and a reusable pipeline (resultant elimination plus Macaulay-matrix
ideal-membership certificates checked by `linear_combination`) for fixed-degree polynomial
systems.
