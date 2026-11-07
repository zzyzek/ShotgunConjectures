# Short guides: quadratic discriminants, squared rectangles, combinatorial lines, decimal digits, small lemmas

Modules: `R5_Quadratic.lean`, `SquaredRect.lean`, `D_CombLine.lean`, `Digits10.lean`, `Misc.lean`.

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

---

## Decimal digits, periodic powers of 10, repunits (`Digits10.lean`)

### 1. The method

Builds a decimal number from blocks of digits and controls its digit sum and its residue mod $n$.
Three facts. (a) If $a < 10^m$, the digits of $a + 10^m b$ are those of $a$, padded with zeros to
$m$ places, followed by those of $b$, so $\operatorname{ds}(a + 10^m b) = \operatorname{ds}(a) +
\operatorname{ds}(b)$ ($\operatorname{ds}$ = digit sum). (b) The powers of 10 mod $n$ are eventually
periodic: $10^{i+P} \equiv 10^i \pmod n$ for some $i$ and $P \ge 1$, and then
$10^{i+c+Pt} \equiv 10^{i+c}$ for all $c, t$. (c) A block $Y$ of $L$ digits repeated $k$ times has
value $Y \cdot (1 + 10^L + \dots + 10^{L(k-1)})$, and if $\gcd(m, 10) = 1$ some such base-$10^L$
repunit with $k \ge 2$ ones is divisible by $m$.

### 2. When to reach for it

A claim that some multiple of $n$ has a prescribed digit pattern (begins or ends with given
digits, is a palindrome, has a given digit sum), proved by an explicit construction from digit
blocks.

### 3. Paper proof

(a) Mathlib's `Nat.digits_append_zeroes_append_digits`. (b) Pigeonhole on $10^0, \dots, 10^n$ mod $n$;
the shifted statement by induction on $t$. (c) Let $B = 10^L$ and $M = m(B - 1)$. Then $B$ is coprime
to $m$ (as $\gcd(m,10) = 1$) and to $B - 1$, so $B^{\varphi(M)} \equiv 1 \pmod M$ (Euler). With
$k = 2\varphi(M) \ge 2$, $M \mid B^k - 1 = (1 + B + \dots + B^{k-1})(B - 1)$, and cancelling $B - 1$
gives $m \mid 1 + B + \dots + B^{k-1}$. (Classical.)

### 4. Worked example: OEIS A084043

[A084043](https://oeis.org/A084043): least palindromic multiple of $n$ containing the digits of $n$
with at least one digit on each side; conjecture: $a(n) = 0$ iff $10 \mid n$. Write $n = g m$,
$g = 2^a 5^b$, $\gcd(m, 10) = 1$. The block $Y = \operatorname{rev}(E)\, s\, \operatorname{rev}(s)\, E$
($s$ the digits of $n$, $E$ those of $g$ padded to $a + b + 1$ places) is a palindrome whose value
is $\equiv g \pmod{10^{a+b+1}}$, so $g \mid Y$; by (c) some repeat count makes $m$ divide the repunit
factor, so $n$ divides the repeated block. For $n = 7$ ($g = 1$, $L = 1$): $7 \mid 111111$ (6 ones;
the lemma's count $2\varphi(63) = 72$ is larger), and the least value is $a(7) = 777$. For
$n = 12$: $a(12) = 82128 = 12 \cdot 6844$. Lean: `A084043.A084043_main`, `A084043.A084044_main` in
[`OEIS/A084043/A084043_mathlib.lean`](../../OEIS/A084043/A084043_mathlib.lean). OEIS A077739 uses
(a) and (b): digit blocks $1, 10, 100$ spaced $3P$ places apart starting at $10^i$ give a multiple of
$n$ with any digit sum $r$ in the right class mod 9 (for $n = 12$: $10^i \bmod 12 = 1, 10, 4, 4, \dots$,
so $i = 2$, $P = 1$); see [`OEIS/A077739/A077739_mathlib.lean`](../../OEIS/A077739/A077739_mathlib.lean).

### 5. In Lean

`import OpenProblemsLib.Digits10`; namespace `OpenProblemsLib.Digits10`. Digit lists are
`Nat.digits 10` (least significant first), digit sums `(Nat.digits 10 x).sum`.

| declaration | content |
|---|---|
| `digitSum_add` | $a < 10^m$ ⟹ $\operatorname{ds}(a + 10^m b) = \operatorname{ds}(a) + \operatorname{ds}(b)$; e.g. $\operatorname{ds}(25017) = 8 + 7$ |
| `digitSum_le` | $\operatorname{ds}(x) \le 9 + \lfloor x/10 \rfloor$ |
| `pow_period`, `pow_period_mul` | $\exists\, i, P > 0$: $10^{i+P} \equiv 10^i \pmod n$; then $10^{i+c+Pt} \equiv 10^{i+c}$ |
| `rp Y k`, `rp_comm`, `rp_reverse`, `mem_rp` | $k$ copies of the list $Y$; reversal gives $k$ copies of $\operatorname{rev} Y$ |
| `rep B k`, `rep_mul` | $1 + B + \dots + B^{k-1}$; $\operatorname{rep}(B, k)(B - 1) + 1 = B^k$ |
| `ofDigits_rp` | value of `rp Y k` $=$ value of $Y$ times `rep (10^|Y|) k` |
| `dvd_rep` | $\gcd(m,10) = 1$, $L \ge 1$ ⟹ $m \mid$ `rep (10^L) (j+2)` for some $j$ |

Repo files using it: OEIS/A077739 (also A077740), A084043 (also A084044).

---

## Small lemmas: descending factorials, squares mod $p$ (`Misc.lean`)

### 1. The method

Two unrelated single-purpose facts. (a) $n(n-1)\cdots(n-k+1)$ is monotone in $k$ for $k \le n$, so a
bound on the least qualifying $k$ bounds the product. (b) For a prime $p > 3$ and nonzero
$a, b, C \in \mathbb Z/p$, some $a(bx^2 - C)$ is a non-square: a quadratic polynomial cannot map
all squares to squares.

### 2. When to reach for it

(a) A "least product $n(n-1)\cdots$" definition with a known qualifying $k$. (b) Showing a number
is not of a given quadratic form (polygonal, sum of a square and a constant) by a local
obstruction at one prime, then CRT over several primes.

### 3. Paper proof

(a) Each extra factor $n - l \ge 1$. (b) Let $S$ be the set of squares in $\mathbb Z/p$. Every nonzero
square has exactly two roots $\pm y$ ($2 \ne 0$), so $\sum_x x^2 = 2 \sum_{s \in S} s$, and
$\sum_x x^2 = 0$ for $p > 3$; hence $\sum_{s \in S} s = 0$. If $f(s) = a(bs - C)$ sent $S$ into $S$, it
would permute $S$ ($f$ is injective, $ab \ne 0$), so $\sum_S f(s) = \sum_S s$, i.e.
$ab \cdot 0 - |S| a C = 0$. But $0 < |S| < p$ (a non-square exists), contradiction. (Classical.)

### 4. Worked example: OEIS A176948 (and A096123)

[A176948](https://oeis.org/A176948): for $n \ge 4$, $n \ne 6$, some $n$-gonal number is not $k$-gonal
for any $3 \le k < n$. A common value of $P_n(j)$ and $P_k(i)$ forces $a(bX^2 - C)$ to be a square
($a = n - 2$, $b = k - 2$, $X = 2aj - (a - 2)$, $C = (a - b)(ab - 4)$); (b) gives a residue of $j$
mod a prime $p_k > n^3$ that breaks this, and CRT combines the $k$. Small case: $p = 5$, $a = b = C = 1$:
$x^2 - 1 \bmod 5$ takes the values $4, 0, 3, 3, 0$, and $3$ is not a square ($S = \{0, 1, 4\}$, sum $5 \equiv 0$).
Lean: `A176948_conjecture` in [`OEIS/A176948/A176948_mathlib.lean`](../../OEIS/A176948/A176948_mathlib.lean).
[A096123](https://oeis.org/A096123) uses (a): at $n = 2p$, $k = p$ qualifies ($p!\,p! \mid (2p)!$), so
$a(2p) \le (2p)!/p! < (2p)!/(p-1)!$; for $n = 10$: $a(10) = 10 \cdot 9 \cdot 8 \cdot 7 = 5040 \le 30240 < 151200$.
Lean: `A096123_main` in [`OEIS/A096123/A096123_mathlib.lean`](../../OEIS/A096123/A096123_mathlib.lean).

### 5. In Lean

`import OpenProblemsLib.Misc`; namespace `OpenProblemsLib.Misc`. Primes enter as `[Fact p.Prime]`.

| declaration | content |
|---|---|
| `descFactorial_mono` | $k \le l \le n$ ⟹ `n.descFactorial k ≤ n.descFactorial l` |
| `two_ne_zero_zmod` | $p > 2$ ⟹ $(2 : \mathbb Z/p) \ne 0$ |
| `sum_squares_zero` | $p > 3$ ⟹ $\sum_{s \in S} s = 0$, $S$ the image of $x \mapsto x^2$ |
| `exists_nonsq` | $p > 3$, $a, b, C \ne 0$ ⟹ $\exists x$, $a(bx^2 - C)$ not a square |

Repo files using it: OEIS/A096123, A176948.
