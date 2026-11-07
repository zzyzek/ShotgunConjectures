# Number-theoretic witnesses as kernel checks

Modules: `PowMod.lean`, `Pratt.lean`, `Fermat.lean`, `Korselt.lean`, `Cipolla.lean`.

## 1. The method

Many claims about pseudoprimes and Carmichael numbers are settled by a finite witness: a
factorization, a base $b$ with $b^{n-1} \equiv 1 \pmod n$, a primality certificate. The method
turns each witness into a Boolean function on natural-number literals, proves once that the
function returning `true` implies the mathematical property, and lets the Lean kernel evaluate
the function (`decide +kernel`). No `native_decide` is involved, so the trusted base is the
kernel with its GMP-accelerated `+`, `*`, `/`, `%` on literals.

Notation. $n, b, p, q$ are natural numbers; $p, q$ denote primes where stated.
$n$ is a *probable prime to base $b$* if $n \mid b^{n-1} - 1$ (Mathlib `Nat.ProbablePrime n b`),
a *Fermat pseudoprime to base $b$* if moreover $n > 1$ is composite (`Nat.FermatPsp n b`), and a
*Carmichael number* if $n > 2$ is composite and a probable prime to every base coprime to $n$
(`Nat.IsCarmichael n`).

**Modular exponentiation (PowMod).** `powMod a e m` is square-and-multiply, and
$$\mathtt{powMod}(a, e, m) = a^e \bmod m \quad\text{for all } a, e, m \in \mathbb N.$$
It makes about $\log_2 e$ recursive calls, each a product and a remainder of numbers below $m^2$.
The plain term `a ^ e % m` cannot be evaluated by the kernel for large $e$ because `Nat.pow` is
unfolded $e$ times.

**Pratt certificates (Pratt).** A step $\langle p, a, [(q_1,k_1),\dots,(q_r,k_r)]\rangle$ is
accepted when
$$p \ge 2,\qquad p - 1 = \prod_i q_i^{k_i},\qquad a^{p-1} \equiv 1 \pmod p,\qquad
a^{(p-1)/q_i} \not\equiv 1 \pmod p \ (1 \le i \le r),$$
and every $q_i$ is the $p$ of an earlier accepted step. A certificate is a list of steps
accepted in order. Theorem: every $p$ in an accepted certificate is prime.

**Fermat pseudoprimes (Fermat).** For $b \ge 1$, $n \ge 2$:
$n$ is a probable prime to base $b$ iff $\mathtt{powMod}(b, n-1, n) = 1$.
`pspCheck n b d` adds a proper divisor $2 \le d < n$, $d \mid n$, and so certifies
`Nat.FermatPsp n b`. A second statement constrains prime factors: if $p$ is prime, $p \mid N$,
$p \nmid b$ and $N$ is a probable prime to base $b$, then
$$p \mid b^{\gcd(p-1,\,N-1)} - 1,$$
hence $p \mid b^m - 1$ whenever $\gcd(p-1, N-1) \mid m$.

**Korselt's criterion (Korselt).** For $n \in \mathbb N$,
$$n \text{ is Carmichael} \iff n > 2,\ n \text{ composite},\ n \text{ squarefree},\
(p - 1) \mid (n - 1) \text{ for every prime } p \mid n.$$
The library uses the sufficient direction with an explicit factorization: if
$n = p_1 \cdots p_r$ with distinct primes $p_i$, $r \ge 2$ and $p_i - 1 \mid n - 1$ for all $i$,
then $n$ is Carmichael. `carmichaelCheck n ps cert` checks this with the primes certified by a
Pratt certificate. `divisorsList ps` lists all sub-products of a list of primes; every divisor of
$\prod ps$ is in it, so "for every divisor" becomes a finite check.

**Cipolla's pseudoprimes (Cipolla).** For $b \ge 2$ and a prime $p > 2$ with
$p \nmid b(b^2 - 1)$,
$$N = \frac{b^{2p} - 1}{b^2 - 1} = \frac{b^p - 1}{b - 1}\cdot\frac{b^p + 1}{b + 1}$$
is a Fermat pseudoprime to base $b$ and $N > p$. Different $p$ give different $N$, so each base
$b \ge 2$ has infinitely many pseudoprimes.

## 2. When to reach for it

- A claim names a specific number that is (or is not) a pseudoprime, Carmichael number, or prime:
  "3048841 is a Poulet number", "561 is Carmichael", "this 30-digit $p$ is prime".
- A conjecture of the form "every Poulet/Carmichael number with property X also has Y" (many of
  Coman's): a counterexample is one number plus a factorization and one `powMod`.
- "Infinitely many pseudoprimes of the form $(b^{2p}-1)/(b^2-1)$" or a family built from it:
  Cipolla's theorem.
- A statement that a prime factor of a pseudoprime must divide some $b^m - 1$:
  `prime_dvd_pow_sub_one_of_gcd_dvd`.
- A "for all $p, m, n$" statement about factorizations of one fixed number: reduce the unknowns
  to divisors, then check all of `divisorsList`.

## 3. Paper proof

**PowMod.** The loop keeps a triple $(b, e, \mathit{acc})$ and the invariant
$\mathit{acc} \cdot b^e \bmod m$. Writing $e = 2\lfloor e/2\rfloor + (e \bmod 2)$,
$$\mathit{acc}\cdot b^e = \bigl(\mathit{acc}\cdot b^{\,e \bmod 2}\bigr)\cdot (b^2)^{\lfloor e/2\rfloor},$$
and reducing $\mathit{acc}\cdot b^{e \bmod 2}$ and $b^2$ modulo $m$ does not change the right side
modulo $m$. At $e = 0$ the invariant is $\mathit{acc} \bmod m$. Starting from
$(a \bmod m, e, 1)$ gives $a^e \bmod m$. (Square-and-multiply is classical; the kernel-facing
formulation with a fuel argument is ours.)

**Lucas test, hence Pratt.** Let $p \ge 2$, $a^{p-1} \equiv 1$ and
$a^{(p-1)/q} \not\equiv 1 \pmod p$ for every prime $q \mid p - 1$. Then $a$ is a unit mod $p$;
let $t$ be its order. $t \mid p - 1$. If $t < p - 1$, some prime $q$ divides $(p-1)/t$, so
$t \mid (p-1)/q$ and $a^{(p-1)/q} \equiv 1$, a contradiction. So $t = p - 1$, the unit group of
$\mathbb Z/p$ has at least $p - 1$ elements, every nonzero residue is a unit, and $p$ is prime.
In a certificate step the primes $q \mid p - 1$ are among the $q_i$ because
$p - 1 = \prod q_i^{k_i}$ and the $q_i$ are prime (certified earlier); induction along the list
gives primality of every step. (Lucas 1876; certificates and their polynomial size: V. Pratt,
*Every prime has a succinct certificate*, SIAM J. Comput. 4 (1975). The soundness step is
Mathlib's `lucas_primality`; the Boolean checker is ours.)

**Probable primes and `powMod`.** For $b \ge 1$, $n \mid b^{n-1} - 1$ iff
$b^{n-1} \equiv 1 \pmod n$ iff $b^{n-1} \bmod n = 1$ (as $n \ge 2$). A divisor $2 \le d < n$
shows $n$ composite.

**Prime factors of a probable prime.** In $\mathbb Z/p$, $b \ne 0$, so $b^{p-1} = 1$
(Fermat). From $p \mid N \mid b^{N-1} - 1$, $b^{N-1} = 1$. The exponents $e$ with $b^e = 1$ form
the multiples of the order of $b$, which divides both $p-1$ and $N-1$, hence their gcd $g$; so
$b^g = 1$. If $g \mid m$ then $b^g - 1 \mid b^m - 1$.

**Korselt.** ($\Leftarrow$) Let $\gcd(a, n) = 1$ and $p \mid n$. Then
$a^{p-1} \equiv 1 \pmod p$ and $p - 1 \mid n - 1$ give $a^{n-1} \equiv 1 \pmod p$. Since $n$ is
squarefree, it is the product of its prime divisors and $a^{n-1} \equiv 1 \pmod n$.
($\Rightarrow$) Suppose $p^2 \mid n$. By the Chinese remainder theorem pick $a$ with
$a \equiv 1 + p \pmod{p^2}$ and $a \equiv 1$ modulo the part of $n$ prime to $p$; then $a$ is
coprime to $n$ and $a^{n-1} \equiv 1 \pmod{p^2}$. But $(1+p)^k \equiv 1 + kp \pmod{p^2}$, so
$p \mid n - 1$, impossible as $p \mid n$. So $n$ is squarefree. For $p \mid n$ pick $a$ a
primitive root mod $p$ and $\equiv 1$ modulo $n/p$; $a^{n-1} \equiv 1 \pmod p$ forces
$p - 1 \mid n - 1$. (A. Korselt, 1899. Both directions are Mathlib's
`Nat.isCarmichael_iff_korselt`; the library uses them and adds the Boolean check.)
For an explicit list: a product of $r \ge 2$ distinct primes is $> 2$, composite, squarefree, and
its prime divisors are exactly the listed primes, so the sufficient direction applies.

**Sub-products.** Induction on the list $p :: t$: if $p \mid d$, write $d = p e$ with
$e \mid \prod t$; otherwise $\gcd(p, d) = 1$ and $d \mid \prod t$.

**Cipolla.** Let $A = (b^p - 1)/(b - 1)$, $B = (b^p + 1)/(b + 1)$ (integers; $p$ odd), and
$N = AB = (b^{2p} - 1)/(b^2 - 1)$. $A = 1 + b + \dots + b^{p-1} > p$ and $B \ge 2$, so $N$ is
composite and $N > p$. Next,
$$(b^2 - 1)(N - 1) = b^{2p} - b^2 = b\,(b^{p-1} - 1)\,(b^p + b).$$
Fermat gives $p \mid b^{p-1} - 1$; $p - 1$ is even, so $b^2 - 1 \mid b^{p-1} - 1$; $p \nmid b^2 - 1$,
so $p(b^2 - 1) \mid b^{p-1} - 1$; and $b^p + b$ is even. Hence $2p(b^2 - 1) \mid (b^2 - 1)(N-1)$,
i.e. $2p \mid N - 1$. Finally $N \mid b^{2p} - 1 \mid b^{N-1} - 1$. (M. Cipolla, 1904. The Lean
proofs are copied from Mathlib's `FermatPsp.lean` by N. Voss, where they are private; the
identity `cipollaNum_eq` is exposed here.)

## 4. Worked example: OEIS A215944 (Coman)

**Claim** (comment in [A215944](https://oeis.org/A215944), M. Coman 2012, paraphrased): the only
base-2 Fermat pseudoprimes divisible by a smaller base-2 pseudoprime that cannot be written as
$p\,((m+1)p - m)\,((n+1)p - n)$ with $p, m, n \in \mathbb N$ are multiples of 5461.

**Counterexample.** $P = 3048841 = 61 \cdot 151 \cdot 331$.

1. $P$ is a base-2 pseudoprime: `pspCheck 3048841 2 61`. The kernel computes
   $\mathtt{powMod}(2, 3048840, 3048841) = 1$; $P - 1$ has 22 binary digits, so about 22 squarings.
   On a smaller input, $2^{340} \bmod 341$, the loop runs through $(e, b, \mathit{acc})$:
   $(340,2,1)$, $(170,4,1)$, $(85,16,1)$, $(42,256,16)$, $(21,64,16)$, $(10,4,1)$, $(5,16,1)$,
   $(2,256,16)$, $(1,64,16)$, $(0,4,1)$, ending with $\mathit{acc} = 1$.
2. $Q = 49981 = 151 \cdot 331$ is a base-2 pseudoprime (`pspCheck 49981 2 151`), $Q \mid P$
   ($P = 61Q$) and $Q < P$.
3. $5461 \nmid P$ ($P \bmod 5461 = 1603$).
4. $P$ is not of the form. Since $(m+1)p - m = p + m(p-1)$, for $p \ge 2$ the three factors
   $x = p$, $y = p + n(p-1)$, $z = p + m(p-1)$ satisfy $x \le y$, $x \le z$ and
   $y \equiv z \equiv x \pmod{x - 1}$; $p = 0, 1$ give products 0 and 1. All three divide $P$, so
   they lie in `divisorsList [61, 151, 331]` $= \{1, 61, 151, 331, 9211, 20191, 49981, P\}$.
   The only divisor triples with $xyz = P$, $x \ge 2$, $x \le y$, $x \le z$ are
   $(61, 151, 331)$ and $(61, 331, 151)$, and $151 \equiv 331 \equiv 31 \not\equiv 1 \equiv 61
   \pmod{60}$. The kernel checks all $8^3$ triples.

Lean: main theorem `A215944.A215944_counterexample` in
[`OEIS/A215944/A215944_mathlib.lean`](../../OEIS/A215944/A215944_mathlib.lean):
```
Nat.FermatPsp 3048841 2 ∧ (∃ d, Nat.FermatPsp d 2 ∧ d ∣ 3048841 ∧ d < 3048841) ∧
¬ 5461 ∣ 3048841 ∧ ∀ p m n : ℕ, p * ((m + 1) * p - m) * ((n + 1) * p - n) ≠ 3048841
```
Minimality of the counterexample is checked outside Lean (Python over the Feitsma–Galway list).

A Pratt certificate in the same style (from `lib/test/KorseltTest.lean`): 561 is Carmichael by
`carmichaelCheck 561 [3, 11, 17] cert` with
`cert = [⟨2,1,[]⟩, ⟨3,2,[(2,1)]⟩, ⟨5,2,[(2,2)]⟩, ⟨11,2,[(2,1),(5,1)]⟩, ⟨17,3,[(2,4)]⟩]`.
For example the step for 11: $10 = 2 \cdot 5$, $2^{10} \equiv 1$, $2^{5} \equiv 10$,
$2^{2} \equiv 4 \pmod{11}$. Korselt: $560$ is divisible by $2$, $10$ and $16$.
`tools/pratt_cert.py N ...` prints certificates.

## 5. In Lean

Import one module (`import OpenProblemsLib.Korselt` pulls in `Pratt`, `Fermat`, `PowMod`) or the
whole library (`import OpenProblemsLib`). Everything is in namespace `OpenProblemsLib`. Files are
checked with `tools/leancheck-mathlib.sh` after `tools/buildlib.sh`.

| declaration | content |
|---|---|
| `powMod a e m`, `powMod_eq` | square-and-multiply; `powMod a e m = a ^ e % m` |
| `PrattStep`, `prattCheck cert` | certificate step `⟨p, a, fs⟩`; Boolean check of a list of steps |
| `prattCertifies n cert`, `prime_of_prattCertifies` | `= true → n.Prime` |
| `prattCertifiesAll ns cert`, `primes_of_prattCertifiesAll` | `= true → ∀ n ∈ ns, n.Prime` |
| `probablePrime_iff_powMod` | `1 ≤ b → 2 ≤ n → (ProbablePrime n b ↔ powMod b (n-1) n = 1)` |
| `pspCheck n b d`, `fermatPsp_of_pspCheck` | `= true → n.FermatPsp b` (`d` a proper divisor) |
| `probablePrimeCheck`, `probablePrime_of_check` | probable prime only |
| `not_probablePrime_of_powMod`, `not_fermatPsp_of_powMod` | `powMod b (n-1) n ≠ 1` refutes |
| `prime_dvd_pow_gcd_sub_one`, `prime_dvd_pow_sub_one_of_gcd_dvd` | $p \mid b^{\gcd(p-1,N-1)}-1$; $p \mid b^m - 1$ |
| `korselt`, `korselt_necessary`, `IsCarmichael.squarefree'` | Korselt's criterion (Mathlib) and its parts |
| `isCarmichael_iff_modEq` | Carmichael ↔ $n > 2$, composite, $a^{n-1} \equiv 1$ for all $a$ coprime to $n$ |
| `isCarmichael_of_factors` | sufficient condition for an explicit list of distinct primes |
| `carmichaelCheck n ps cert`, `isCarmichael_of_carmichaelCheck` | the same as a Boolean check with Pratt-certified primes |
| `factorCheck`, `of_factorCheck`, `squarefree_of_factorCheck` | `n = ∏ ps`, distinct certified primes; squarefree, `primeFactors = ps` |
| `squarefree_of_primes`, `mem_of_prime_dvd_prod`, `primeFactors_eq_of_primes` | factorization helpers |
| `exists_sublist_of_dvd_prod`, `divisorsList`, `mem_divisorsList_of_dvd` | every divisor of a product of primes is a sub-product |
| `dvd_sub_one_of_eq` | `N = (f-1) Q + 1 → f - 1 ∣ N - 1` |
| `not_isCarmichael_of_powMod` | a coprime base with `powMod b (n-1) n ≠ 1` refutes Carmichael |
| `cipollaNum b p`, `cipollaNum_eq` | $AB$; equals $(b^{2p}-1)/(b^2-1)$ for odd $p$ |
| `cipolla_fermatPsp`, `cipolla_gt`, `cipolla` | Cipolla's theorem |

Kernel cost: `decide +kernel` on `prattCheck` or `pspCheck` is proportional to the number of
`powMod` calls times $\log_2$ of the exponent; repo certificates reach primes of about 125 digits.
`divisorsList` has $2^r$ entries for $r$ primes, so a check over all triples costs $8^r$.

Repo files using these modules (by declaration names; directory per problem):

- PowMod: COM/C006, C011, C042, C086, C088, C091, C108, C116, C123, C124, P122, P126, P127;
  FAM/wieferich-composite; OEIS/A182207, A214074, A214305, A215672, A215944.
- Pratt: COM/C006, C011, C012, C019, C044, C045, C088, C089, C091, C099, C103, C108, C116, C123,
  C125, C173, C180, P016, P018, P022, P040, P044, P062, P122; FAM/wieferich-composite;
  NT/A3.9, B1.2, B4.3; OEIS/A051451, A088120, A212843.
- Fermat: COM/C006, C032, C058, C086, C088, P122, P126, P127; OEIS/A214305, A215672, A215944.
- Korselt: COM/C006, C011–C017, C019, C042, C044, C045, C088, C089, C091, C099, C103, C108, C116,
  C123, C124, C173, C180, P016, P018, P022, P040, P044, P062, P122; OEIS/A182085, A182088, A182089,
  A182132, A182133, A182151, A182206, A182207, A182208, A182381, A182416, A182515, A182532,
  A212843, A214758, A215672, A215944. (`carmichaelCheck` itself is used only in
  `lib/test/KorseltTest.lean`; problem files call `isCarmichael_of_factors` with
  `primes_of_prattCertifiesAll`.)
- Cipolla: COM/C003, C050, C162.
