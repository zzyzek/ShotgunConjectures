# Hankel determinants of constant-term sequences (`MomentHankel.lean`)

## 1. The method

Let $L$ be a Laurent polynomial in several variables with real coefficients and
$L(1/x_1, \dots, 1/x_m) = L(x_1, \dots, x_m)$. Put $a(k) = \operatorname{CT}(L^k)$ (constant term).
If $1, L, \dots, L^{n-1}$ are linearly independent, the Hankel matrix $[a(i+j)]_{0 \le i,j < n}$ is
positive definite, so its determinant is positive.

## 2. When to reach for it

A claim that Hankel determinants $\det[a(i+j)]$ are positive (or that $a$ is a moment sequence),
where $a(k)$ counts something that is a constant term of a power: sums of products of binomial
coefficients ($\sum_j \binom kj^r$, Franel and Apéry-like numbers), central coefficients
($\binom{2k}{k} = \operatorname{CT}((x + 2 + 1/x)^k)$), lattice-walk returns. Symmetry
$L(1/x) = L(x)$ is the only structural input; it replaces the usual "the measure is real and
positive" step, and needs no roots of unity, cosines or integrals.

## 3. Paper proof

Let $\sigma$ be the ring map $x^e \mapsto x^{-e}$. For any $Q$, the constant term of
$Q \cdot \sigma(Q)$ is $\sum_e Q_e Q_e$, the sum of the squares of the coefficients of $Q$. For a real
vector $c$ put $Q = \sum_i c_i L^i$. Since $\sigma L = L$, $\sigma Q = Q$, and
$$c^T [a(i+j)] c = \sum_{i,j} c_i c_j \operatorname{CT}(L^{i+j}) = \operatorname{CT}(Q^2)
= \operatorname{CT}(Q\, \sigma Q) = \sum_e Q_e^2 \ge 0,$$
with equality only if $Q = 0$, that is (by independence) only if $c = 0$.

Linear independence is usually shown by evaluation: a ring map $\mathrm{ev}_t$ to $\mathbb R$ sends
$Q$ to $p(\mathrm{ev}_t L)$ with $p = \sum_i c_i X^i$; if $\mathrm{ev}_t L$ takes $n$ distinct
values, the Vandermonde matrix is invertible and $c = 0$
(`Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero`).

## 4. Worked example: OEIS A225776

$f(r,k) = \sum_j \binom kj^r$ is the constant term of $L^k$ with
$L = (1+x_1)\cdots(1+x_{r-1})(1 + 1/(x_1 \cdots x_{r-1}))$: choosing $x_i^{a_i}$ from
$(1+x_i)^k$ and $(x_1\cdots x_{r-1})^{-b}$ from the last factor, the constant term forces
$a_i = b$, with coefficient $\binom kb^r$. $L(1/x) = L(x)$ because
$\prod (1+x_i) = (x_1 \cdots x_{r-1}) \prod(1 + 1/x_i)$. At $x_1 = t$, $x_2 = \dots = 1$,
$L = 2^{r-2}(2 + t + 1/t)$, which is injective on $t = 1, 2, \dots$. Hence
$\det[f(r, i+j)]_{0 \le i,j \le n} > 0$ for all $r \ge 2$. File:
`OEIS/A225776/A225776_mathlib.lean` (`ct_Lr_pow`, `refl_Lr`, `Lr_indep`, `A225776_pos`).

## 5. Lean declarations (`namespace OpenProblemsLib.MomentHankel`)

Laurent polynomials are `AddMonoidAlgebra ℝ G` for an additive commutative group `G`
(`G = Fin m → ℤ`).

| declaration | statement |
|---|---|
| `ct P` | `P.coeff 0` |
| `negRefl` | ring hom `AddMonoidAlgebra ℝ G →+* AddMonoidAlgebra ℝ G`, exponent `g ↦ -g` |
| `refl_single` | `negRefl (single g c) = single (-g) c` |
| `coeff_refl_neg` | `(negRefl P).coeff (-g) = P.coeff g` |
| `refl_smul` | `negRefl (a • P) = a • negRefl P` |
| `ct_sum`, `ct_smul` | linearity of `ct` |
| `ct_mul` | `ct (P * R) = ∑ a ∈ P.coeff.support, P.coeff a * R.coeff (-a)` |
| `ct_mul_self_of_refl` | `negRefl Q = Q → ct (Q * Q) = ∑ a ∈ Q.coeff.support, Q.coeff a ^ 2` |
| `ct_mul_self_pos` | `negRefl Q = Q → Q ≠ 0 → 0 < ct (Q * Q)` |
| `form_eq` | the `Finsupp` quadratic form in `Matrix.PosDef` as a double `Fin` sum |
| `hankel_posDef` | `negRefl L = L → (∀ c, ∑ i, c i • L ^ i = 0 → c = 0) → (Matrix.of fun i j : Fin n => ct (L ^ (i + j))).PosDef` |

Then `Matrix.PosDef.det_pos` gives the determinant, and `RingHom.map_det` with `Int.cast_pos`
moves an integer Hankel matrix to `ℝ`. Evaluation maps come from
`AddMonoidAlgebra.lift ℝ ℝ G φ` with `φ : Multiplicative G →* ℝ` (see `phi`, `ev`, `ev_Lr` in the
A225776 file).

Used by: OEIS A225776.
