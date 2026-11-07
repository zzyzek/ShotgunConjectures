# Sums over ℤ/n and maps that miss one residue

Module: `ModularSums.lean`.

## 1. The method

If $n - 1$ objects are sent injectively into $\mathbb Z/n$, the image misses exactly one residue
$a$, so the sum of any function $g$ over the objects is the full sum $\sum_{v \in \mathbb Z/n} g(v)$
minus $g(a)$. Applying this to several injective maps at once, with $g(v) = v$ and $g(v) = v^2$,
gives linear and quadratic relations between the missing residues, which often contradict a
congruence for $\sum_{i<n} i^2$. For even $n$, squares are only well defined modulo $2n$ after
lifting, and a lifting lemma handles that.

Notation. $S$ is a finite set with $|S| = n - 1$, $f : S \to \mathbb Z/n$ injective, $g$ maps
$\mathbb Z/n$ to an abelian group $R$.

- (`sum_zmod`) $\displaystyle\sum_{v \in \mathbb Z/n} g(v) = \sum_{i=0}^{n-1} g(i \bmod n)$.
- (`miss`) There is $a \in \mathbb Z/n$ such that for every abelian group $R$ and every
  $g : \mathbb Z/n \to R$,
  $$\sum_{x \in S} g(f(x)) = \sum_{v \in \mathbb Z/n} g(v) - g(a).$$
  The same $a$ works for all $g$ (it is the missing residue).
- (`sq_lift`) If $2 \mid n$ and $u, w \in \mathbb Z$ with $u \equiv w \pmod n$, then
  $u^2 \equiv w^2 \pmod{2n}$.

## 2. When to reach for it

- A maximum-size question on the torus $\mathbb Z/n \times \mathbb Z/n$ (queens, permutations,
  orthomorphisms, complete mappings) where the conjectured answer is $n - 1$ or $n - 2$: assume
  $n - 1$ objects and use "each coordinate map misses one value".
- Several linear functions of the coordinates are all injective (rows, columns, diagonals,
  anti-diagonals), and an identity such as $(x+y)^2 + (y-x)^2 = 2x^2 + 2y^2$ links them.
- The contradiction is a divisibility of $\sum_{i<n} i^2 = (n-1)n(2n-1)/6$ that fails for
  $3 \mid n$ or $4 \mid n$.

## 3. Paper proof

`sum_zmod`: $i \mapsto i \bmod n$ is a bijection $\{0, \dots, n-1\} \to \mathbb Z/n$.

`miss`: $f(S)$ has $n - 1$ elements (injectivity), so its complement in $\mathbb Z/n$ is a single
residue $a$. Then $\sum_{x \in S} g(f(x)) = \sum_{v \in f(S)} g(v) = \sum_{v} g(v) - g(a)$.

`sq_lift`: write $u = w + nt$ and $n = 2r$. Then $u^2 = w^2 + 2nwt + n^2t^2$ and
$n^2 t^2 = 2n \cdot r t^2$, so $u^2 \equiv w^2 \pmod{2n}$.

These are elementary; the way they combine below is P. Monsky's (solution to problem E3162,
Amer. Math. Monthly 96 (1989) 258–259). The Lean lemmas are ours.

## 4. Worked example: NT-C18.4 (Guy C18, Monsky's modular queens)

**Claim** (Guy, *Unsolved Problems in Number Theory*, C18, paraphrased). On the $n \times n$ board
whose rows, columns and diagonals wrap around, the maximum number $M(n)$ of non-attacking queens is
$n - 2$ when $3 \mid n$ or $4 \mid n$. Queens at $(x, y)$ and $(x', y')$ in
$\mathbb Z/n \times \mathbb Z/n$ attack iff $x = x'$, $y = y'$, $x + y = x' + y'$ or
$y - x = y' - x'$.

**Upper bound from the module.** Suppose $S$ is a non-attacking set with $|S| = n - 1$. The four
maps $x$, $y$, $x+y$, $y-x$ are injective on $S$; `miss` gives missing residues $a, b, c, d$. Let
$T = \sum_{v \in \mathbb Z/n} v$; $T = -T$ (negation permutes $\mathbb Z/n$), so $2T = 0$.

- Linear sums ($g(v) = v$): $\sum (x + y) = \sum x + \sum y$ gives $T - c = (T - a) + (T - b)$, so
  $c = a + b - T$; similarly $d = T - a + b$.
- Squares ($g(v) = v^2$, $Q = \sum_v v^2$): $\sum (x+y)^2 + \sum (y-x)^2 = 2\sum x^2 + 2\sum y^2$
  gives $2Q - c^2 - d^2 = 4Q - 2a^2 - 2b^2$. Substituting $c, d$:
  $c^2 + d^2 = 2a^2 + 2b^2 - 4Ta + 2T^2$, hence $2Q = 2T(2a - T) = 0$ in $\mathbb Z/n$.
- With `sum_zmod`, $2Q = 2\sum_{i<n} i^2 = (n-1)n(2n-1)/3$ as an integer, so
  $3n \mid (n-1)n(2n-1)$, i.e. $3 \mid (n-1)(2n-1)$. If $3 \mid n$ then
  $(n-1)(2n-1) \equiv 1 \pmod 3$: contradiction.
- If $4 \mid n$ the congruence mod $n$ can hold, so the same computation is done in
  $\mathbb Z/2n$ with lifts $L(v) \in \{0, \dots, n-1\}$; `sq_lift` makes $L(x+y)^2$ equal to
  $(L(x) + L(y))^2$ modulo $2n$, and $2T = 0$ in $\mathbb Z/n$ gives $L(T) \in \{0, n/2\}$. Both
  cases give $2\sum_{i<n} i^2 \equiv 0 \pmod{2n}$, i.e. $6 \mid (n-1)(2n-1)$, false because
  $(n-1)(2n-1)$ is odd.

**Small cases.**

| $n$ | $T \bmod n$ | $\sum_{i<n} i^2$ | $2\sum i^2 \bmod n$ | $2\sum i^2 \bmod 2n$ | $M(n)$ (brute force) |
|---|---|---|---|---|---|
| 4 | 2 | 14 | 0 | 4 | 2 |
| 6 | 3 | 55 | 2 | 2 | 4 |
| 12 | 6 | 506 | 4 | 4 | 10 (Lean) |

For $n = 6$ the mod-$n$ step already gives $110 \equiv 2 \not\equiv 0$; for $n = 4$ it gives
$28 \equiv 0 \pmod 4$ and only the mod-8 step ($28 \equiv 4$) excludes 3 queens.

The lower bound (explicit placements of $n - 2$ queens, K. Williams, arXiv:2404.18237) is proved in
the same file without this module.

Lean: `NT_C18_4.modular_queens_eq` in
[`NT/C18.4/C18_4_mathlib.lean`](../../NT/C18.4/C18_4_mathlib.lean); the upper bound is
`no_n_minus_one` and `queens_upper`:
```
theorem modular_queens_eq (n : ℕ) (hn : 3 ≤ n) (hd : 3 ∣ n ∨ 4 ∣ n) :
    (∃ S : Finset (ZMod n × ZMod n), S.card = n - 2 ∧ NonAttacking S) ∧
    ∀ S : Finset (ZMod n × ZMod n), NonAttacking S → S.card ≤ n - 2
```

## 5. In Lean

`import OpenProblemsLib.ModularSums` (it imports all of Mathlib) or `import OpenProblemsLib`;
namespace `OpenProblemsLib.ModularSums`.

| declaration | content |
|---|---|
| `sum_zmod g` | $\sum_{v : \mathbb Z/n} g(v) = \sum_{i < n} g(i)$, for `[NeZero n]` and any additive commutative monoid |
| `miss S f hf hc` | `Set.InjOn f S`, `S.card + 1 = n` ⟹ `∃ a, ∀ R g, ∑ p ∈ S, g (f p) = ∑ v, g v - g a` (`R : Type`, an additive commutative group) |
| `sq_lift hn u w h` | `2 ∣ n`, `(u : ZMod n) = w` ⟹ `(u : ZMod (2n))^2 = (w : ZMod (2n))^2` |

Repo files using it: NT/C18.4.
