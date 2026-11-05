# Famous open problems: weaker results

Well-known open problems (from the Wikipedia list of unsolved problems, MathWorld and Guy). The problems stay open; each entry is a weaker result (special case, bound, or formalisation of a known partial result) and the obstacle the attempt hit.

8 entries: 0 resolved by this project, 0 answered elsewhere, 0 disputed or partial.

Of the 0 resolutions: 0 proved in full in Lean, 0 with the finite facts (witnesses) checked in Lean and the remaining steps on paper, 0 on paper only (re-derived by a second reader; 0 of these need Mathlib to formalise).

Columns: **Lean** says how far Lean checks the result (`full proof`: the whole statement; `witness`: the finite facts, with the steps outside Lean named in the problem README; `needs Mathlib`: written proof only). **Prior art** (review 2026-11-04, sources in each problem README): `new` = no source found stating the answer, `partly-known`, `known`; "(immediate)" = follows in a few lines from a known theorem. **Verdict**: proved, disproved, or trivial/misstated. **Result**: one-line summary. **Method** links to [methods/](../methods/README.md). Each problem directory holds the README (source, reading, result, argument, evidence, review level, prior art), the Lean file and `certificate/` scripts.

## Weaker results on open problems (the problem stays open)

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [casas-alvero](casas-alvero/) | partial | Casas-Alvero conjecture in degrees 2 to 6, in Lean (FAM-casas-alvero) | [full proof](casas-alvero/casas_alvero_mathlib.lean) | known | [macaulay-ideal-membership](../methods/macaulay-ideal-membership/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [dean-cycles](dean-cycles/) | partial | Dean's conjecture, k = 5 status and longest-path lemmas in Lean (FAM-dean-cycles) | [full proof](dean-cycles/dean_cycles_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [goormaghtigh](goormaghtigh/) | partial | Goormaghtigh's equation, exponent pairs (3, 5) and (3, 7) (FAM-goormaghtigh) | [full proof](goormaghtigh/goormaghtigh_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [lehmer-totient](lehmer-totient/) | partial | Lehmer's totient problem (FAM-lehmer-totient) and the cube-count core (OEIS-A123365) | [full proof](lehmer-totient/lehmer_totient_mathlib.lean) | known | [ordered-prime-gap-bound](../methods/ordered-prime-gap-bound/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [odd-perfect](odd-perfect/) | partial | Odd perfect numbers (FAM-odd-perfect) | [full proof](odd-perfect/odd_perfect_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [sumner-tournament](sumner-tournament/) | partial | Sumner's universal tournament conjecture for n ≤ 5 (FAM-sumner-tournament) | [full proof](sumner-tournament/sumner_tournament_mathlib.lean) | known | [lean-certificate](../methods/lean-certificate/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [twin-primes](twin-primes/) | partial | Brun's theorem and a uniform prime-pair bound in Lean | [full proof](twin-primes/twin_primes_mathlib.lean) | partly-known | [selberg-sieve-polynomial](../methods/selberg-sieve-polynomial/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [wieferich-composite](wieferich-composite/) | partial | Composite c with 2^(c-1) ≡ 1 (mod c^2) (FAM-wieferich-composite) | [full proof](wieferich-composite/wieferich_composite_mathlib.lean) | partly-known | [cofactor-exponent](../methods/cofactor-exponent/README.md), [lean-certificate](../methods/lean-certificate/README.md) |

## Short proofs

Copied from each problem README (source paraphrase, result, argument).

### [casas-alvero](casas-alvero/): Casas-Alvero conjecture in degrees 2 to 6, in Lean (FAM-casas-alvero)

Lean: [full proof](casas-alvero/casas_alvero_mathlib.lean).

### [dean-cycles](dean-cycles/): Dean's conjecture, k = 5 status and longest-path lemmas in Lean (FAM-dean-cycles)

Lean: [full proof](dean-cycles/dean_cycles_mathlib.lean).

### [goormaghtigh](goormaghtigh/): Goormaghtigh's equation, exponent pairs (3, 5) and (3, 7) (FAM-goormaghtigh)

Lean: [full proof](goormaghtigh/goormaghtigh_mathlib.lean).

### [lehmer-totient](lehmer-totient/): Lehmer's totient problem (FAM-lehmer-totient) and the cube-count core (OEIS-A123365)

Lean: [full proof](lehmer-totient/lehmer_totient_mathlib.lean).

### [odd-perfect](odd-perfect/): Odd perfect numbers (FAM-odd-perfect)

Lean: [full proof](odd-perfect/odd_perfect_mathlib.lean).

### [sumner-tournament](sumner-tournament/): Sumner's universal tournament conjecture for n ≤ 5 (FAM-sumner-tournament)

Lean: [full proof](sumner-tournament/sumner_tournament_mathlib.lean).

### [twin-primes](twin-primes/): Brun's theorem and a uniform prime-pair bound in Lean

**Source.** Twin prime conjecture (Wikipedia, Landau's problems; MathWorld TwinPrimeConjecture;
formal-conjectures `FormalConjectures/Wikipedia/TwinPrimes.lean`, tagged `research open`, no
`formal_proof`). Famous-problem pilot, problem 2 of 6.

**Result.** The conjecture itself is untouched (it is blocked by the parity problem of sieves).
Proved in Lean 4 + Mathlib, unconditionally:

| Theorem | Statement |
|---|---|
| `brun_summable` | `Summable twinTerm`, where `twinTerm n = 1/n` if `n` and `n + 2` are prime, else `0` (Brun 1919). |
| `twinCount_le` | For `N ≥ 2`: `#{p < N : p, p + 2 prime} ≤ 2^28 N / (log N)^2`. |
| `pairCount_le_log` | For every even `h > 0` and `N ≥ 2`: `#{p < N : p, p + h prime} ≤ 2^13 K(h)^2 N / (log N)^2`, with `K(h) = ∏_{p ∣ h} p/(p-1) = h/φ(h)`. Uniform in `h`. |
| `pairCount_le_uniform` | The underlying sieve inequality: for even `h > 0`, any `N` and `w ≥ 1`, the count is at most `w^4 + 1 + K(h)^2 N / log(w+1)^2 + w^16`. |
| `pairCount_le` | An earlier, weaker form with `h^2` in place of `K(h)^2` (level `(hM)^4`). |

`K(h)^2` replaces the singular series `∏_{p ∣ h, p > 2} (p-1)/(p-2)` of the sharp bound
(Halberstam–Richert Thm 3.11). Both are `≍ (h/φ(h))^{O(1)} ≪ (log log h)^{O(1)}`. The constants
`2^28`, `2^13` are far from optimal (the sharp Selberg constant is 8 times the twin-prime
constant).

**Argument.** Selberg's Λ² sieve applied to the sequence `n (n + h)`, `n < N`, sifting by the
primes `≤ Y = w^4`.
1. Local densities. `ρ(d) = #{x mod d : x (x + h) ≡ 0}` is multiplicative (Chinese remainder theorem,
   `ZMod.chineseRemainder`); `ρ(p) = 1` if `p ∣ h`, `ρ(p) = 2` otherwise, so `ν(d) = ρ(d)/d` and
   `ν(p) < 1` because `h` is even.
2. Remainders. `n ↦ [d ∣ n (n + h)]` has period `d`, so `|#{n < N : d ∣ n(n+h)} - ρ(d) N / d| ≤ ρ(d) ≤ d`.
   With the Selberg weights `|μ⁺(d)| ≤ 3^ω(d) ≤ d^2`, the error sum over `d ≤ Y` is at most `Y^4`.
3. Main term. `S = ∑_{l ∣ P, l^2 ≤ Y} g(l)` with `g(p) = ν(p)/(1 - ν(p))`. Since `x/(1-x)` increases,
   `g(l) ≥ ∏_{p ∣ l} f(p)/(1 - f(p))` for the completely multiplicative `f(n) = 2^Ω(n)/n` on `n`
   coprime to `h` (0 otherwise). Expanding the geometric series gives `S ≥ ∑_{m ≤ w^2} f(m)`
   (the argument of PrimeNumberTheoremAnd's `selbergBoundingSum_ge_sum_div`, generalised from
   `f = ν` to `f ≤ ν`). Then `f(m) ≥ τ(m)/m` (`τ ≤ 2^Ω`), so
   `∑_{m ≤ w^2} f(m) ≥ (∑_{a ≤ w, (a,h)=1} 1/a)^2`. Removing one prime of `h` at a time
   (`a = p^e b`) gives `∑_{a ≤ w} 1/a ≤ K(h) ∑_{a ≤ w, (a,h)=1} 1/a`, and `∑_{a ≤ w} 1/a ≥ log(w+1)`
   (Mathlib `log_add_one_le_harmonic`). So `S ≥ (log(w+1)/K(h))^2`.
4. Count. Primes `p > Y` with `p + h` prime survive the sieve, so the count is
   `≤ Y + 1 + N/S + Y^4`. Taking `w = 2^j` with `20 j ≈ log_2 N` gives the `(log N)^2` form.
5. Brun. Blocks `[2^{20j}, 2^{20j+20})` contribute `≤ 2^25 / j^2` to `∑ 1/p`; partial sums are bounded,
   `summable_of_sum_range_le`.

Lean: [full proof](twin-primes/twin_primes_mathlib.lean).

### [wieferich-composite](wieferich-composite/): Composite c with 2^(c-1) ≡ 1 (mod c^2) (FAM-wieferich-composite)

Lean: [full proof](wieferich-composite/wieferich_composite_mathlib.lean).

