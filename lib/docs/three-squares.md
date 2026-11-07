# Three squares: Legendre's theorem (Gauss 1801, Dirichlet's proof)

Module: `ThreeSquares.lean`.

## 1. The method

Mathlib has the two-square and four-square theorems but not the three-square theorem. The module
proves it:

$$n = x^2 + y^2 + z^2 \text{ is solvable in integers} \iff n \text{ is not of the form } 4^a(8b+7).$$

The hard direction goes through ternary quadratic forms. A positive definite integral ternary
form of determinant 1 is a sum of three squares of integral linear forms. So $n$ is a sum of
three squares as soon as some such form has $n$ as a diagonal coefficient. Dirichlet's theorem on
primes in progressions builds that form. Minkowski's convex body theorem (Mathlib) replaces
Gauss's reduction theory.

**Notation.** For integers $a, b, c, d, e, g$ the form `qf a b c d e g` is
$Q(x) = x^\top A x$ with $A = \begin{pmatrix} a & b & c\\ b & d & e\\ c & e & g\end{pmatrix}$, `bf` is the
bilinear form $x^\top A y$ and `det3` is $\det A$.

**Theorem** (`ThreeSquares.lean`).

1. If $A$ is real with $a > 0$, $ad - b^2 > 0$ and $0 < \det A \le 2$, some nonzero
   $x \in \mathbb Z^3$ has $Q(x) < 2$ (`exists_small`).
2. If $A$ is integral with $a > 0$, $ad - b^2 > 0$ and $\det A = 1$, then $g$ is a sum of three
   integer squares (`sum_three_sq_of_det_one`).
3. If $n \equiv 1, 2, 3, 5, 6 \pmod 8$ then $n$ is a sum of three integer squares
   (`sum_three_sq_of_mod_eight`).
4. $x^2 + y^2 + z^2 \ne 4^a(8b+7)$ for natural $x, y, z, a, b$ (`not_sum_three_sq`).
5. Over $\mathbb N$, $(\exists x\,y\,z,\ x^2+y^2+z^2 = n) \iff \neg\exists a\,b,\ n = 4^a(8b+7)$
   (`sum_three_sq_iff`). Over $\mathbb Z$ the right side is
   $0 \le n \wedge \neg\exists a\,b,\ n = 4^a(8b+7)$ (`sum_three_sq_iff_int`).

## 2. When to reach for it

- Problems that need some representation as a sum of three squares, or as three squares plus
  another term. Peel off the extra term so that the remainder avoids $4^a(8b+7)$. Examples are
  sums of three squares and a fourth power (A214900), and three triangular numbers
  ($8n + 3 = x^2 + y^2 + z^2$ with $x, y, z$ odd, which is forced mod 8).
- Problems that need $n$ itself to avoid $4^a(8b+7)$, through the easy direction (item 4).
- Not for counting representations. The number $r_3(n)$ is given by Gauss's class-number
  formula, which the module does not contain. A047926 needs $r_3(9^n)$ and stays open in Lean.
- Not for representations with side conditions such as positivity, prescribed residues of
  $x, y, z$, or "for all large $n$" with few representations. Those need class-number lower
  bounds or equidistribution (Duke–Schulze-Pillot), as in A223732 and NT-C20.4.

## 3. Paper proof

Source: the route of Dirichlet and Landau, as in M. B. Nathanson, *Additive Number Theory: The
Classical Bases*, §1.4–1.5. Minkowski's theorem replaces Gauss reduction.

**Step 1: unimodular forms (items 1–2).** Write $m = ad - b^2$ and $D = \det A$. Completing the
square gives
$a\,m\,Q(x) = m(ax_0 + bx_1 + cx_2)^2 + (m x_1 + (ae - bc)x_2)^2 + aD\,x_2^2$ (`qf_ldl`). So
$Q(x) = \lVert Sx\rVert^2$ for an upper triangular $S$ with $\det S = \sqrt{D}$. The ellipsoid
$\{Q < 2\}$ is convex and symmetric, with volume $\frac{4\pi}{3}\, 2^{3/2}/\sqrt D \ge
\frac{8\pi}{3} > 8$ for $D \le 2$. Minkowski's theorem for $\mathbb Z^3$ (covolume 1) gives item 1.

Now let $A$ be integral with $\det A = 1$. Then $Q(x) \ge 1$ for $x \ne 0$.
- Item 1 gives $v$ with $Q(v) = 1$.
- The form $Q(x) + B(v, x)^2$ has matrix $A + (Av)(Av)^\top$, of determinant
  $\det A\,(1 + Q(v)) = 2$. Item 1 gives $w \ne 0$ with $Q(w) + B(v,w)^2 \le 1$, so $B(v,w) = 0$
  and $Q(w) = 1$.
- Put $t = Av \times Aw$. Then $B(v,t) = B(w,t) = 0$, and
  $Q(t) = \det A\,(Q(v)Q(w) - B(v,w)^2) = 1$. All three facts are polynomial identities.
- The matrix $P = [v\ w\ t]$ has $P^\top A P = I$. Hence $P P^\top A = I$, and
  $Q(x) = \lVert P^\top A x\rVert^2$ for every $x$. At $x = e_3$ this gives $g = Q(e_3)$ as a sum
  of three squares.

**Step 2: the form for $n$ (item 3).** Suppose there are $d > 0$ and $t$ with $N = dn - 1 > 0$
and $N \mid t^2 + d$. Put $a = (t^2 + d)/N$. The matrix
$\begin{pmatrix} a & t & 1\\ t & N & 0\\ 1 & 0 & n\end{pmatrix}$ has $a > 0$, $aN - t^2 = d > 0$ and
determinant $n d - N = 1$, so step 1 applies with $g = n$. To get $d$ and $t$:
- $n \equiv 2 \pmod 4$. Dirichlet gives a prime $p \equiv n - 1 \pmod{4n}$, and $p = dn - 1$ with
  $d \equiv 1 \pmod 4$, $p \equiv 1 \pmod 4$. Then
  $\left(\frac{-d}{p}\right) = \left(\frac{d}{p}\right) = \left(\frac{p}{d}\right) = \left(\frac{-1}{d}\right) = 1$.
- $n$ odd, $n \not\equiv 7 \pmod 8$. Take $c = 1$ for $n \equiv 3$ and $c = 3$ for
  $n \equiv 1, 5 \pmod 8$. Dirichlet gives a prime $p \equiv (cn - 1)/2 \pmod{4n}$, so $2p = dn - 1$
  with $d \equiv c \pmod 8$. From $2p \equiv -1 \pmod d$ we get
  $\left(\frac 2d\right)\left(\frac pd\right) = \left(\frac{-1}{d}\right)$, hence $\left(\frac pd\right) = 1$.
  Reciprocity then gives $\left(\frac{-d}{p}\right) = 1$ when $p \equiv 1 \pmod 4$. When
  $p \equiv 3 \pmod 4$ we have $d \equiv 3 \pmod 4$, and the two signs cancel. A root $t$ of
  $t^2 \equiv -d \pmod p$ is made odd by adding $p$. Then $2p \mid t^2 + d$.

**Step 3 (items 4–5).** Squares are $0, 1, 4 \pmod 8$, so $8b + 7$ is not a sum of three squares.
If $4 \mid x^2 + y^2 + z^2$ then $x, y, z$ are all even, which gives the descent in $a$. For the
converse, multiples of 4 reduce to $n/4$, and the remaining $n$ satisfy item 3.

## 4. Worked example: A214900

**Claim** ([A214900](https://oeis.org/A214900), Sun's conjecture). Every $n$ is
$x^2 + y^2 + z^2 + w^4$.

**Proof.** If $n$ is not $4^a(8b+7)$, take $w = 0$ (item 5). If $a = 0$, then $n - 1 = 8b + 6$. If
$a = 1$, then $n - 1 = 32b + 27$. Neither has the form $4^{a'}(8b'+7)$, so $w = 1$ works. If
$a \ge 2$, then $n = 16m$, and induction gives $m = x^2+y^2+z^2+w^4$, so
$n = (4x)^2 + (4y)^2 + (4z)^2 + (2w)^4$.

**Lean.** `OEIS/A214900/A214900_mathlib.lean`: `A214900_legendre` (item 5, hard direction) and
`A214900_main`.

## 5. Lean names

| name | statement |
|---|---|
| `qf`, `bf`, `det3`, `av`, `cr` | the form, its bilinear form, determinant, $Ax$, cross product |
| `qf_ldl` | completing the square with denominators cleared |
| `volume_unit_ball3` | volume of $\{\sum z_i^2 < 1\} \subset \mathbb R^3$ is $4\pi/3$ |
| `exists_small` | Minkowski: $0 < \det \le 2$ gives $x \in \mathbb Z^3 \setminus 0$ with $Q(x) < 2$ |
| `exists_small_int`, `qf_pos_int` | the integer form of `exists_small`; positive definiteness |
| `sum_three_sq_of_det_one` | $\det A = 1$, $a > 0$, $ad - b^2 > 0$ ⟹ $g = y_0^2 + y_1^2 + y_2^2$ |
| `exists_prime_eq` | Dirichlet: a prime $p = 4nj + r$ for $r$ coprime to $4n$ |
| `exists_sq_of_jacobi` | $J(D \mid p) = 1$ ⟹ $p \mid t^2 - D$ for some $t$ |
| `key_two_mod_four`, `key_odd` | the pair $(d, t)$ for $n \equiv 2 \pmod 4$ and for odd $n \not\equiv 7 \pmod 8$ |
| `sum_three_sq_of_key` | $(d, t)$ ⟹ $n$ is a sum of three squares |
| `sum_three_sq_of_mod_eight` | item 3 |
| `not_sum_three_sq` | item 4 |
| `sum_three_sq_iff`, `sum_three_sq_iff_int` | item 5 |

All in namespace `OpenProblemsLib.ThreeSquares`; axioms propext, Classical.choice, Quot.sound.
Used by OEIS A214900.
