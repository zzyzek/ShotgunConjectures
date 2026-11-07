# Automatic sequences modulo prime powers: Cartier operators on diagonals

Modules: `AutomaticMod.lean` (the method), `HannaMod4.lean` (worked instance, Lagrange inversion).

## 1. The method

A sequence given as the diagonal `a(n) = [xⁿ tⁿ] F` of a rational bivariate series `F` over `ℤ/p^a` is
`p`-automatic (Christol, Denef–Lipshitz); Rowland and Yassawi ("Automatic congruences for diagonals of
rational functions", J. Théor. Nombres Bordeaux 27 (2015)) make the automaton explicit. The module proves
the operator identities behind it over any commutative ring and supplies a computable model of
bivariate polynomials, so that a concrete automaton (finitely many numerators, closed under the steps) is
checked by `decide`, and an induction on `n` turns it into a statement about every `a(n)`.

**Notation.** `R⟦X⟧⟦X⟧` with outer variable `x` and inner variable `t`. `cart p r f = ∑ₙ f_{pn+r} Xⁿ` (one
variable), `cart2 p r F` with `[xⁱ tʲ] cart2 p r F = [x^(pi+r) t^(pj+r)] F`, `sig2 p hp F = F(x^p, t^p)`,
`diag F n = [xⁿ tⁿ] F`.

**Theorem** (`AutomaticMod.lean`).

1. `cart_mul_expand`, `cart2_mul_sig2`: for `r < p`, `Λ_r(G · H(x^p, t^p)) = Λ_r(G) · H`.
2. `diag_cart2`: `diag (cart2 p r F) n = diag F (p n + r)`.
3. `ry_step`: let `U · U⁻¹ = 1`, `sig2 U = M · U`, and let `e₁ … e_k` be series with
   `M eᵢ = ∑ⱼ cᵢⱼ · sig2 eⱼ`. Then for all `Nᵢ`,
   `cart2 ((∑ᵢ Nᵢ eᵢ) U⁻¹) = (∑ⱼ cart2 (∑ᵢ Nᵢ cᵢⱼ) eⱼ) U⁻¹`.
   For `U = Q^(p^(a-1))`, `M = Q^(p^a - p^(a-1))` over `ℤ/p^a` the hypothesis `sig2 U = M U` is the congruence
   `Q^(p^a) ≡ Q(x^p, t^p)^(p^(a-1))`; with `e = (1)` this is the Rowland–Yassawi step on numerators.
   Extra basis series `eᵢ` admit non-rational factors (for instance a lacunary `W` with
   `(1-t)(W + W(t²)) = t`).
4. `automaton_induction`: if `f s (p n + r) = f (δ s r) n` for `r < p`, a set `S` of states is closed under
   `δ`, and `P (f s 0)` for `s ∈ S`, then `P (f s n)` for all `n` and `s ∈ S`.
5. List model (`p = 2`): `ps2 : List (List R) → R⟦X⟧⟦X⟧` with `ps2_add2`, `ps2_mul2`, `ps2_sig2L`,
   `ps2_half2` (`Λ_r` on lists), `ps2_trim2` (trailing zeros removed). A step on numerators is a list
   computation; equal trimmed lists give equal series.

**Trusted surface.** The statement of the final theorem (the sequence and the claim). Not trusted: the
script that found the states, the state literals (they are checked by `decide`).

## 2. When to reach for it

- OEIS claims "a(n) is never ≡ r (mod p^a)", "a(n) is odd iff …", base-`p` patterns of `a(n) mod p^a`, for
  algebraic generating functions or binomial sums.
- The work is the link from the problem's definition to a diagonal: Lagrange inversion for a one-variable
  substitution `x = φ(t)` gives `a(n) = [tⁿ] H(t) ψ(t)ⁿ = [xⁿ tⁿ] H(t)/(1 - x ψ(t))`; binomial sums
  `∑_k C(αn + βk, …)` are diagonals directly. The automaton itself is cheap (six states, `decide` in seconds).
- Moduli `p^a` with `a ≥ 2`: numerators carry `Q^(p^a - p^(a-1))`; degrees stay below
  `deg N ≤ (deg N + (p^a - p^(a-1)) deg Q)/p`, so the state space is finite but can be large for big `a`.
- Not for statements that mix two sequences pointwise in a non-automatic way (products of automatic
  sequences are fine: run the product automaton).

## 3. Paper proof

**Cartier identity.** `[t^(pn+r)] (G · H(t^p)) = ∑_{i + pj = pn + r} gᵢ hⱼ = ∑_{j ≤ n} g_{p(n-j)+r} hⱼ`
since `r < p` forces `i ≡ r (mod p)`; this is `[tⁿ] Λ_r(G) H`. In two variables apply it in `x` (coefficients
in `R⟦t⟧`) and then in `t`, coefficientwise and additively.

**Step.** `sig2` is a ring hom, so `sig2 U · sig2 U⁻¹ = 1`, `M U · sig2 U⁻¹ = 1` and
`U⁻¹ = M · sig2 U⁻¹`. Then `(∑ Nᵢ eᵢ) U⁻¹ = ∑ᵢ Nᵢ (M eᵢ) sig2 U⁻¹ = ∑ⱼ (∑ᵢ Nᵢ cᵢⱼ) sig2 (eⱼ U⁻¹)`, and the
Cartier identity gives the claim.

**Automaton.** Strong induction on `n`: `n = p ⌊n/p⌋ + (n mod p)` and `⌊n/p⌋ < n` for `n > 0`.

## 4. Worked example: OEIS A183161, A218622, A219197

**Claim.** If `a(0) = 1` and `∑_k a(k) a(n-k) = A183160(n) = ∑_k C(n+k, n-k) C(2n-k, k)`, then
`a(n) ≢ 3 (mod 4)`. The same for A199033 (A219197).

**Link** (`HannaMod4.lean`). `lagrange`: `[xⁿ] F = [tⁿ] F(t(1-t)²) (1-3t) (1-t)^(-2n-1)` (check on monomials
`xᵐ`, `m ≤ n`: `C(3d, d) = 3 C(3d-1, d-1)`). `fibT_closed`:
`(1+t) ∑_k C(N-k, k) tᵏ (1-t)^(N-2k) = 1 - (-t)^(N+1)`, so `A183160(n) = [tⁿ] (1-t)^(-2n-1)/(1+t)`
(`A183160_eq`). Injectivity of `H ↦ ([tⁿ] H (1-t)^(-2n-1))ₙ` (`kernel_inj`) then gives
`a(n) = [tⁿ] S (1-t)^(-2n-1)` with `S(0) = 1`, `S² (1+t) = 1-3t`; `S_mod4`: `S ≡ 1 + 2W (mod 4)` with
`W = ∑ {tᵐ : m ≥ 1, v₂(m) even}`.

**Automaton.** `a(n) ≡ [xⁿ tⁿ] (N₀ + N₁ W)/Q²` over `ℤ/4`, `Q = (1-t)((1-t)² - x)`, `N₀ = (1-t)² Q`,
`N₁ = 2N₀`; basis `e = (1, W)`, `U = M = Q²` (`frob_ok`: `Q⁴ = Q(x², t²)²` by `decide`), relation
`Q² W = t(1-t)B² · 1 - Q² · W(t²)` (`he`). The script `OEIS/A183161/certificate/ry_automaton.py` finds six
numerator pairs `st`; `step_ok` (by `decide`) checks the transitions (0,0,3,4,4,5) on digit 0 and
(1,2,2,5,3,5) on digit 1; the values at 0 are `1, 1, 2, 2, 2, 0` (`out_ok`). A219197 starts in state 1.

**Lean.**

```lean
theorem A183161_mod4 (a : ℕ → ℤ) (h0 : a 0 = 1)
    (hconv : ∀ n, ∑ k ∈ Finset.range (n + 1), a k * a (n - k) =
      ∑ k ∈ Finset.range (n + 1), (((n + k).choose (n - k) * (2 * n - k).choose k : ℕ) : ℤ))
    (n : ℕ) : a n % 4 ≠ 3
```

in `OEIS/A183161/A183161_mathlib.lean`, from `OpenProblemsLib.HannaMod4.A183161_def_mod4`.

## 5. Lean names

| name | statement or role |
|---|---|
| `cart`, `coeff_cart`, `cart_mul_expand` | one-variable Cartier operator and its key identity |
| `cart2`, `sig2`, `oexp`, `cart2_mul_sig2` | two-variable Cartier operator, Frobenius substitution |
| `diag`, `diag_cart2` | diagonal and `d(pn + r) = diag(Λ_r F)(n)` |
| `ry_step` | Rowland–Yassawi step with a Frobenius basis |
| `automaton_induction` | finite closed state set gives the claim for all `n` |
| `ps1`, `ps2`, `add1`, `mul1`, `add2`, `mul2`, `sig1`, `sig2L`, `evens`, `odds`, `half2`, `trim1`, `trim2` | computable list model and its `ps`-lemmas |
| `HannaMod4.lagrange`, `kernel_inj`, `fibT_closed`, `A183160_eq`, `A199033_eq` | Lagrange inversion for `x = t(1-t)²` and the link to the definitions |
| `HannaMod4.S_mod4`, `st`, `δ`, `step_ok`, `frob_ok`, `f_ne_three` | the six-state automaton |
| `HannaMod4.A183161_def_mod4`, `A219197_def_mod4`, `gf_mod4`, `hanna_mod4` | main results |

All in namespaces `OpenProblemsLib.AutomaticMod`, `OpenProblemsLib.HannaMod4`; axioms propext,
Classical.choice, Quot.sound. Used by OEIS-A183161, OEIS-A218622, OEIS-A219197.
