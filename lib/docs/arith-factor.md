# σ, d, φ and unitary divisors from a factorization

Module: `ArithFactor.lean`.

## 1. The method

To evaluate a divisor function at a large explicit $n$, write $n$ as a list of prime powers and
compute the function as a product over the list. The module proves, for Mathlib's own
definitions, that the product formulas are correct once the bases are checked to be distinct
primes; the kernel then evaluates the products. It also lists the unitary divisors of $n$ as
sub-products of the prime-power list, which turns "no unitary divisor of $n$ has property X" into
a finite check.

Notation. A factor list $f = [(p_1, e_1), \dots, (p_r, e_r)]$ stands for
$\operatorname{val} f = \prod_i p_i^{e_i}$. $f$ is *valid* (`FactOK f`) if the $p_i$ are prime and
pairwise distinct. $\sigma(n) = \sum_{d \mid n} d$, $d(n) = \#\{d : d \mid n\}$, $\varphi$ is Euler's
totient. A divisor $d$ of $n$ is *unitary* if $\gcd(d, n/d) = 1$.

For valid $f$:
$$\sigma(\operatorname{val} f) = \prod_{i=1}^r \bigl(1 + p_i + \dots + p_i^{e_i}\bigr),\qquad
d(\operatorname{val} f) = \prod_{i=1}^r (e_i + 1),$$
$$\varphi(\operatorname{val} f) = \prod_{i=1}^r p_i^{e_i - 1}(p_i - 1)\quad\text{if all } e_i \ge 1,$$
and every unitary divisor of $\operatorname{val} f$ equals $\operatorname{val} s$ for a sublist $s$
of $f$ (keep or drop each whole prime power).

The Lean statement for unitary divisors is this one direction only. The converse (every
sub-product is a unitary divisor) is true but not in the module, and there is no function for the
unitary divisor sum $\sigma^*$.

Validity is checked by `factCheck`: distinct bases and each base prime by trial division up to
$\sqrt p$ (`primeTD`). Trial division costs about $\sqrt p$ kernel steps, so it suits bases up to
roughly $10^6$; larger prime bases need a Pratt certificate (see [certificates.md](certificates.md)).

## 2. When to reach for it

- A claim about $\sigma(n)$, $d(n)$, $\varphi(n)$ or $n\,d(n)/\sigma(n)$ (harmonic numbers) for a
  specific large $n$ with known factorization: abundance, perfection, amicable pairs, harmonic
  means.
- A claim that quantifies over the unitary divisors of a specific number ("seed", "primitive",
  "no smaller unitary divisor with X"): enumerate the $2^r$ sub-products.
- Any claim where $n$ is too large to enumerate its divisors but $r$ (the number of distinct primes)
  is small.

## 3. Paper proof

$\sigma$, $d = \sigma_0$ and $\varphi$ are multiplicative: $F(ab) = F(a)F(b)$ for coprime $a, b$.
For valid $f = (p, e) :: f'$, $p^e$ is coprime to $\operatorname{val} f'$ because $p$ is prime and
differs from every base of $f'$. So $F(\operatorname{val} f) = F(p^e)\,F(\operatorname{val} f')$,
and induction on the list reduces to prime powers:
$\sigma(p^e) = 1 + \dots + p^e$ (the divisors of $p^e$ are $p^0, \dots, p^e$),
$d(p^e) = e + 1$, $\varphi(p^e) = p^{e-1}(p-1)$ for $e \ge 1$.

Unitary divisors. Let $n = p^e m$ with $\gcd(p, m) = 1$ and $d \mid n$ unitary. Put
$d_1 = \gcd(d, p^e) = p^j$ and $d_2 = \gcd(d, m)$; then $d = d_1 d_2$ and
$n/d = p^{e-j}(m/d_2)$. If $0 < j < e$, $p$ divides both $d$ and $n/d$, contradicting
$\gcd(d, n/d) = 1$; so $j \in \{0, e\}$. And $d_2$ is a unitary divisor of $m$ (a common divisor of
$d_2$ and $m/d_2$ divides $d$ and $n/d$). Induction on $m$ finishes.

These facts are classical (multiplicativity of $\sigma$: Euler; unitary divisors:
R. Vaidyanathaswamy 1931, E. Cohen 1960). Mathlib provides multiplicativity; the list formulation,
the trial-division check and the unitary-divisor classification in Lean are ours.

## 4. Worked example: NT-B2.7 (Guy B2, harmonic seeds)

**Claim** (Guy, *Unsolved Problems in Number Theory*, B2, paraphrased). $n$ is *harmonic* if
$H(n) = n\,d(n)/\sigma(n)$ is an integer. A harmonic $m > 1$ is a *seed* if no unitary divisor $e$ of
$m$ with $1 < e < m$ is harmonic. Goto and Shibata ask whether every harmonic number has a unique
seed among its unitary divisors. Answer: no.

**Witness.** $f = [(2,4),(3,1),(5,2),(7,2),(19,1),(31,2),(83,1),(331,1)]$,
$n = \operatorname{val} f = 29495815011600$. The factors $1 + \dots + p^e$ are
$31, 4, 31, 57, 20, 993, 84, 332$, so
$$\sigma(n) = 31\cdot 4\cdot 31\cdot 57\cdot 20\cdot 993\cdot 84\cdot 332 = 121354210333440,$$
$$d(n) = 5\cdot 2\cdot 3\cdot 3\cdot 2\cdot 3\cdot 2\cdot 2 = 2160,\qquad
H(n) = \frac{29495815011600 \cdot 2160}{121354210333440} = 525.$$
Dropping $5^2$ gives $m_1 = n/25 = 1179832600464$ with $\sigma(m_1) = \sigma(n)/31 = 3914651946240$,
$d(m_1) = 720$, $H(m_1) = 217$. Dropping $3$ gives $m_2 = n/3 = 9831938337200$ with
$\sigma(m_2) = \sigma(n)/4 = 30338552583360$, $d(m_2) = 1080$, $H(m_2) = 350$.

**Seeds.** By the classification, the unitary divisors of $m_1$ are the $2^7 = 128$ sub-products
of its list; the kernel checks that each is $1$, $m_1$, or has $\sigma \nmid \mathrm{val}\cdot d$.
The same for $m_2$. (Of all $2^8$ unitary divisors of $n$, the harmonic ones $> 1$ are exactly
$m_1, m_2, n$.) Both $m_1$ and $m_2$ are unitary divisors of $n$, and $m_1 \ne m_2$.

Lean: `B2_7_main` and `B2_7_false` in
[`NT/B2.7/B2_7_mathlib.lean`](../../NT/B2.7/B2_7_mathlib.lean). The helper `seed_of` there shows
the pattern: `unitary_val` turns a unitary divisor $e$ into a sublist $s$, then `sigma_val` and
`card_divisors_val` on $s$ (valid by `FactOK.sublist`) reduce harmonicity of $e$ to the Boolean
`seedCheck`.

## 5. In Lean

`import OpenProblemsLib.ArithFactor` (or `import OpenProblemsLib`); namespace
`OpenProblemsLib.ArithFactor`. $\sigma$ is Mathlib `ArithmeticFunction.sigma 1`, $d(n)$ is
`n.divisors.card`, $\varphi$ is `Nat.totient`.

| declaration | content |
|---|---|
| `PF`, `val f` | factor list `List (ℕ × ℕ)`; $\prod p^e$ |
| `gsum p e`, `sigF f`, `ndF f`, `phiF f` | $1+\dots+p^e$; the product formulas for $\sigma$, $d$, $\varphi$ |
| `FactOK f`, `factCheck f`, `factOK_of_check` | validity; Boolean check; `= true → FactOK f` |
| `primeTD p`, `prime_of_primeTD` | trial-division primality; `= true → p.Prime` |
| `FactOK.tail`, `FactOK.sublist`, `val_pos` | validity passes to tails and sublists; `0 < val f` |
| `coprime_head` | $\gcd(p^e, \operatorname{val} f') = 1$ for valid $(p,e) :: f'$ |
| `sigma_val` | `FactOK f → sigma 1 (val f) = sigF f` |
| `card_divisors_val` | `FactOK f → (val f).divisors.card = ndF f` |
| `totient_val` | `FactOK f → (∀ pe ∈ f, 0 < pe.2) → φ (val f) = phiF f` |
| `unitary_val` | `FactOK f → d ∣ val f → Coprime d (val f / d) → ∃ s, s.Sublist f ∧ d = val s` |

Repo files using it: NT/B2.7 (σ, d, unitary), NT/B2.8 (σ, d), NT/B10.3 (d, φ); NT/B16.6,
OEIS/A101462, OEIS/A210445 use only `primeTD`.
