# Short guides: quadratic discriminants, squared rectangles, combinatorial lines

Modules: `R5_Quadratic.lean`, `SquaredRect.lean`, `D_CombLine.lean`.

---

## Discriminant of $\mathbb Q(\sqrt d)$ (`R5_Quadratic.lean`)

### 1. The method

Computes Mathlib's `NumberField.discr` (the discriminant of a $\mathbb Z$-basis of the ring of
integers) for quadratic fields by identifying the ring of integers. For a squarefree integer
$d \ne 1$,
$$\operatorname{disc} \mathbb Q(\sqrt d) = \begin{cases} d & d \equiv 1 \pmod 4,\\
4d & d \equiv 2, 3 \pmod 4.\end{cases}$$
More generally, for $K = \mathbb Q[\omega]$ with $\omega^2 = a + b\omega$ ($a, b \in \mathbb Z$, no
rational root), if every element of $K$ integral over $\mathbb Z$ lies in $\mathbb Z[\omega]$ then
$\operatorname{disc} K = b^2 + 4a$.

### 2. When to reach for it

A claim about "the discriminant of $\mathbb Q(\sqrt n)$", fundamental discriminants, or the ring of
integers of a quadratic field, for all $n$ (not one $n$).

### 3. Paper proof

Let $x = s + t\sqrt d$ ($s, t \in \mathbb Q$) be integral over $\mathbb Z$. Its conjugate
$s - t\sqrt d$ is integral, so the trace $2s$ and norm $s^2 - dt^2$ are rational algebraic
integers, hence integers. Then $d(2t)^2 = (2s)^2 - 4(s^2 - dt^2) \in \mathbb Z$; if $d u^2 \in
\mathbb Z$ with $d$ squarefree then $u \in \mathbb Z$ (the square of the denominator of $u$ divides
$d$), so $2t \in \mathbb Z$. Put $S = 2s$, $U = 2t$; $S^2 - dU^2 \equiv 0 \pmod 4$. Squares are
$0, 1 \pmod 4$. If $d \equiv 2, 3 \pmod 4$ this forces $S, U$ even, so $x \in \mathbb Z[\sqrt d]$.
If $d \equiv 1 \pmod 4$ it forces $S \equiv U \pmod 2$, so $x \in \mathbb Z[(1+\sqrt d)/2]$. A
squarefree $d$ is never $\equiv 0 \pmod 4$. For the basis $1, \omega$ the trace matrix is
$\begin{pmatrix} 2 & b \\ b & b^2 + 2a\end{pmatrix}$ with determinant $b^2 + 4a$: for
$\omega = \sqrt d$ ($a = d$, $b = 0$) this is $4d$; for $\omega = (1+\sqrt d)/2$
($a = (d-1)/4$, $b = 1$) it is $d$. (Classical, Dedekind; the Lean proof is ours, built on Mathlib's
`QuadraticAlgebra`.)

### 4. Worked example: OEIS A072901

[A072901](https://oeis.org/A072901) lists composite $n$ with $\operatorname{disc}\mathbb Q(\sqrt n)
= 4n$; conjecture (V. Librandi, M. Marcus): all terms are squarefree. Write $n = s^2 d$ with $d$
squarefree; $\mathbb Q(\sqrt n) = \mathbb Q(\sqrt d)$ has discriminant $d$ or $4d$, at most $4d$, which is
$< 4n$ when $s \ge 2$. Examples: $\operatorname{disc}\mathbb Q(\sqrt 6) = 24 = 4\cdot 6$;
$\operatorname{disc}\mathbb Q(\sqrt{12}) = \operatorname{disc}\mathbb Q(\sqrt 3) = 12 \ne 48$;
$\operatorname{disc}\mathbb Q(\sqrt{20}) = 5$. The composite $n \le 60$ with discriminant $4n$ are
6, 10, 14, 15, 22, 26, 30, 34, 35, 38, 39, 42, 46, 51, 55, 58 (PARI `quaddisc`).
Lean: `A072901_discr` (for non-square $n$: $\operatorname{disc} = 4n$ iff $n$ squarefree and
$n \equiv 2, 3 \pmod 4$) and `A072901_conjecture` in
[`OEIS/A072901/A072901_mathlib.lean`](../../OEIS/A072901/A072901_mathlib.lean).

### 5. In Lean

`import OpenProblemsLib.R5_Quadratic`; namespace `OpenProblemsLib.R5Quadratic`. $\mathbb Q(\sqrt d)$
is `QuadraticAlgebra ℚ d 0`; the field hypothesis is the instance argument
`[Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)]` (or `[Fact (¬ IsSquare (d : ℚ))]` in `discr_sqrt`).

| declaration | content |
|---|---|
| `numberField` | `QuadraticAlgebra ℚ a b` is a number field (instance) |
| `int_of_squarefree_mul_sq` | $d$ squarefree, $d u^2 \in \mathbb Z$ ⟹ $u \in \mathbb Z$ |
| `trace_norm_int` | an integral element has integer trace and norm |
| `closure_zero`, `closure_one` | integral elements lie in $\mathbb Z[\sqrt d]$ ($d \equiv 2,3$), resp. $\mathbb Z[\omega]$, $\omega^2 = a + \omega$ ($d = 1 + 4a$) |
| `isIntegralClosure_of`, `numberField_discr_of` | if $\mathbb Z[\omega]$ contains all integral elements, it is the ring of integers and the discriminant is $b^2 + 4a$ |
| `not_isSquare_of_squarefree`, `emod_four_ne_zero` | squarefree $d \ne 1$ is not a rational square; $d \not\equiv 0 \pmod 4$ |
| `discr_sqrt` | squarefree $d$, not a square: discriminant $d$ if $d \equiv 1 \pmod 4$, else $4d$ |

Repo files using it: OEIS/A072901.

---

## Squared rectangles from a cover certificate (`SquaredRect.lean`)

### 1. The method

Proves that a list of axis-parallel squares with integer sides and corners tiles a $W \times H$
rectangle exactly, as a statement about subsets of $\mathbb R^2$: the union of the closed squares
is $[0, W] \times [0, H]$ and the open squares are pairwise disjoint. The kernel checks a
Boolean certificate; one topological step (closure) is proved once.

A square $\langle s, x, y\rangle$ is $[x, x+s] \times [y, y+s]$. `tilingCheck W H l` checks:
$W, H > 0$; every side positive; every square inside the rectangle; every two squares separated
along $x$ or along $y$; and for every unit column $[i, i+1]$, $i < W$, a chain of squares that span
the column ($x \le i < x + s$) and whose $y$-intervals cover $[0, H)$ from the bottom up. Theorem:
`tilingCheck W H l = true` implies `IsTiling W H l`.

### 2. When to reach for it

A claim about a specific squared rectangle or squared square (perfect, simple, with a property of
its squares), where the witness is a list of squares and the claim needs an exact tiling.

### 3. Paper proof

Inside-ness gives union $\subseteq$ rectangle. Separation along one axis makes the open squares
disjoint. For $(u, v) \in [0, W) \times [0, H)$ put $i = \lfloor u \rfloor$; the chain for column $i$
has a square with $y \le v < y + s$, and $x \le i \le u < i + 1 \le x + s$, so $(u, v)$ is covered.
The union of finitely many closed squares is closed and contains $[0, W) \times [0, H)$, hence its
closure $[0, W] \times [0, H]$. (Squared rectangles go back to Z. Moroń, 1925; the certificate
and proof are ours.)

### 4. Worked example: GEO-C2.1 (Croft–Falconer–Guy C2)

Moroń asked whether every squared rectangle has at least two squares surrounded by larger ones.
The order-9 perfect rectangle $61 \times 69$ with squares $2, 5, 7, 9, 16, 25, 28, 33, 36$ (corners
in the Lean file) has exactly one, the square of side 2. Area check:
$2^2 + 5^2 + 7^2 + 9^2 + 16^2 + 25^2 + 28^2 + 33^2 + 36^2 = 4209 = 61 \cdot 69$. Column $i = 36$
is covered by the chain of sides $25$ ($y \in [0,25]$), $9$ ($[25,34]$), $2$ ($[34,36]$), $5$
($[36,41]$), $28$ ($[41,69]$). Lean: `C2_1_main` (`IsTiling 61 69 c21`, distinct sides, surrounded
squares exactly `[2]`) in [`GEO/C2.1/C2_1_mathlib.lean`](../../GEO/C2.1/C2_1_mathlib.lean).

### 5. In Lean

`import OpenProblemsLib.SquaredRect`; namespace `OpenProblemsLib.SquaredRect`.

| declaration | content |
|---|---|
| `Sq`, `Sq.toSet`, `Sq.inner` | square $\langle s, x, y\rangle$; closed and open square in `ℝ × ℝ` |
| `IsTiling W H l` | positive sides, union $= [0,W]\times[0,H]$, pairwise disjoint interiors |
| `inside`, `apart`, `pairwiseApart`, `spans`, `colOK` | Boolean pieces of the check |
| `tilingCheck W H l`, `tiling_of_check` | `= true → IsTiling W H l` |
| `apart_disjoint`, `pairwise_of_check`, `colOK_spec` | the three steps of the proof |

`IsTiling` does not require distinct sides; perfectness is a separate `Nodup` check on the sides.
Repo files using it: GEO/C2.1, GEO/C2.2, GEO/C2.3.

---

## Collinear $k$-subsets of the grid $\{0, \dots, k-1\}^n$ (`D_CombLine.lean`)

### 1. The method

For $k \ge 2$, a set of exactly $k$ points of the grid $[k]^n = \{0, \dots, k-1\}^n$ that is
collinear in $\mathbb R^n$ is a *combinatorial line*: along it each coordinate is constant, runs
$0, 1, \dots, k-1$, or runs $k-1, \dots, 0$, and not all coordinates are constant. Each line has two
such descriptions (one per direction). Hence
$$\#\{\text{collinear } k\text{-subsets of } [k]^n\} = \frac{(k+2)^n - k^n}{2}
= \sum_{j \text{ odd}} \binom n j (k+1)^{n-j},$$
the second form being the $(k+1)$-th binomial transform of $0, 1, 0, 1, \dots$.

### 2. When to reach for it

"Number of collinear $k$-tuples in the $k \times k \times \dots \times k$ grid", lines of the $k^n$
tic-tac-toe board, or an OEIS entry that is a binomial transform of $0,1,0,1,\dots$ with such a
comment. It covers only sets of exactly $k$ points in the grid of side $k$.

### 3. Paper proof

A description assigns to each coordinate a constant (k ways), "up" or "down": $(k+2)^n$ choices,
$k^n$ of them all constant. Reversing the direction (swap up/down) gives the same set, and a
non-constant description differs from its reversal. Conversely let $S$ be collinear, $|S| = k$,
$S \subset x + \mathbb R v$. Pick $i$ with $v_i \ne 0$; then $p \mapsto p_i$ is injective on $S$,
so it takes all $k$ values $0, \dots, k-1$. Label the points $P_0, \dots, P_{k-1}$ with
$(P_s)_i = s$; the line parameter is affine in $s$, so each coordinate $(P_s)_j$ is an affine
function of $s$ with integer slope $(P_1)_j - (P_0)_j$ and values in $[0, k-1]$ for
$s = 0, \dots, k-1$. The slope is $-1$, $0$ or $1$, starting at $k-1$, anywhere, or $0$
respectively. So $S$ is a line, and two descriptions of the same set are equal or reverses. Each
line is counted twice. The binomial form: $(m+1)^n - (m-1)^n = 2\sum_{j \text{ odd}} \binom nj
m^{n-j}$ with $m = k+1$. (The count of lines of the $k^n$ board is classical; the Lean proof is
ours.)

### 4. Worked example: OEIS A081199

[A081199](https://oeis.org/A081199) is the 5th binomial transform of $0,1,0,1,\dots$; R. H. Hardin
conjectured it counts collinear 4-tuples in the $4^n$ grid. With $k = 4$: $a(n) = (6^n - 4^n)/2$.
For $n = 2$: $(36 - 16)/2 = 10$ (4 rows, 4 columns, 2 diagonals) and $\binom 21 5^1 = 10$. Brute
force also gives $8$ for $(n,k) = (2,3)$, $49$ for $(3,3)$, $12$ for $(2,5)$, matching the formula.
Lean: `A081199_main` in [`OEIS/A081199/A081199_mathlib.lean`](../../OEIS/A081199/A081199_mathlib.lean),
a direct instance of `card_collinear` with `k := 4`.

### 5. In Lean

`import OpenProblemsLib.D_CombLine`; namespace `OpenProblemsLib.D_CombLine`. The grid is
`Fin n → Fin k`, embedded in `Fin n → ℝ` by `emb`; collinearity is Mathlib `Collinear ℝ`.

| declaration | content |
|---|---|
| `Desc n k`, `NonConst`, `pt`, `lineSet`, `flip` | descriptions, their points and set, reversal |
| `collinear_lineSet`, `card_lineSet` | a line is collinear and has $k$ points |
| `exists_desc` | a collinear $k$-subset ($k \ge 2$) is `lineSet f` for a non-constant `f` |
| `eq_or_flip` | two descriptions of one line are equal or reverses |
| `card_nonConst` | $(k+2)^n - k^n$ non-constant descriptions |
| `collinearSets n k`, `two_mul_card_collinear` | the collinear $k$-subsets; twice their number is $(k+2)^n - k^n$ |
| `binomTransform m n`, `two_mul_binomTransform` | $\sum_j \binom nj m^{n-j}[j \text{ odd}]$; twice it is $(m+1)^n - (m-1)^n$ |
| `card_collinear` | count $=$ `binomTransform (k+1) n` $= ((k+2)^n - k^n)/2$ |

Repo files using it: OEIS/A081199 ($k = 4$), A081200 ($k = 5$), A081201 ($k = 6$).
