# Dwork's lemma: Gauss congruences, Euler products and integer exp-log series

Modules: `Dwork.lean`, `DworkEuler.lean`, `DworkMultinomial.lean`, `DworkLocal.lean`,
`DworkLocalPoly.lean`.

## 1. The method

Many OEIS entries define a sequence as the coefficients of $\exp\bigl(\sum_{n \ge 1} b(n) x^n/n\bigr)$
for an explicit integer sequence $b$ and conjecture that the coefficients are integers. Dwork's
lemma turns this into congruences on $b$ alone: the series is integral exactly when
$b(mp^a) \equiv b(mp^{a-1}) \pmod{p^a}$ for every prime $p$. The library proves that equivalence,
closure rules for such $b$, three families of $b$ that satisfy it (a two-variable Euler-product
lemma, "power families", and sums of powers of multinomial coefficients), and a version that works
one prime at a time for rational $b$.

**Notation.** $b : \mathbb N \to \mathbb Z$ (the value $b(0)$ is never used). The coefficients
$A_n = A_n(b)$ of $\exp\bigl(\sum_{n\ge1} b(n)x^n/n\bigr)$ are defined by the recurrence

$$A_0 = 1, \qquad (n+1)\,A_{n+1} = \sum_{j=0}^{n} b(j+1)\,A_{n-j},$$

which is the coefficient form of $x\,E'(x) = \bigl(\sum_{n \ge 1} b(n)x^n\bigr)E(x)$ for
$E = \sum A_n x^n$ (Lean: `expCoeff b n`, a rational number). For a prime $p$, $b$ **satisfies
the Gauss congruences at $p$** if

$$p^a \mid b(mp^a) - b(mp^{a-1}) \quad \text{for all } a \ge 1,\ m \ge 0 \qquad (\texttt{LGp p b}).$$

A **Gauss sequence** satisfies them at every prime.

**Theorem A** (Dwork's lemma, integral form; `Dwork.lean`). For $b : \mathbb N \to \mathbb Z$ the
following are equivalent.

1. $b$ is a Gauss sequence.
2. There are integers $c(d)$ with $b(n) = \sum_{d \mid n} d\,c(d)$ for all $n \ge 1$.
3. $A_n(b) \in \mathbb Z$ for all $n$.

When they hold, $\sum_n A_n x^n = \prod_{d \ge 1} (1 - x^d)^{-c(d)}$, and $c$ is given by the
recursion $n\,c(n) = b(n) - \sum_{d \mid n,\ d < n} d\,c(d)$ (`cOf`).

**Lemma B** (closure; `Dwork.lean`). Gauss sequences at a fixed $p$ are closed under sums,
differences, negation, products, powers $f^k$, finite sums, and contain the constants. If $f$ is
Gauss at $p$ then so are $j \mapsto f(jk)$ for fixed $k$, and $j \mapsto f(j)^{jc}$ for fixed
$c \in \mathbb N$. For $x \in \mathbb Z$, $j \mapsto x^j$ is Gauss at every $p$.

**Theorem C** (the bivariate Euler-product lemma, coefficient form; `DworkEuler.lean`). Let
$F \in \mathbb Z[Y][X]$ (a polynomial in $X$ whose coefficients are polynomials in $Y$), let
$y : \mathbb N \to \mathbb Z$ and $W : \mathbb N^2 \to \mathbb Z$. Put

$$V(m,n) = \frac{m \cdot \bigl([X^m]\,F^n\bigr)(y_n)}{n}, \qquad
\mathrm{rowB}(m) = \sum_{n=0}^{m} W(m,n)\,V(m,n),$$

where $[X^m]F^n \in \mathbb Z[Y]$ is evaluated at $Y = y_n$ (and $V(m,0) = 0$). Assume

- (admissible points, `YCond`) for every prime $p$: $p^e \mid n \Rightarrow p^{e+1} \mid y_{pn}^{\,p} - y_n$;
- (ray congruences, `W1`) for every prime $p$: $p^k \mid m$ and $p^k \mid n \Rightarrow
  p^{k+1} \mid W(pm, pn) - W(m,n)$.

Then $V(m,n) \in \mathbb Z$, $\mathrm{rowB}$ is a Gauss sequence, and
$\exp\bigl(\sum_{m\ge1} \mathrm{rowB}(m)x^m/m\bigr)$ has integer coefficients. The points
$y_n = 0$ and $y_n = q^n$ ($q \in \mathbb Z$) are admissible; $W \equiv 1$ satisfies the ray
congruences, and so does $W(m,n) = u(n)^{\kappa(m,n)}$ whenever $u$ is Gauss at $p$,
$\kappa(pm,pn) = p\,\kappa(m,n)$ and $p^k \mid m, n \Rightarrow p^k \mid \kappa(m,n)$
(`W1_pow`; covers $q^{n(m-n)}$, $q^{mn}$, $L(n)^{m-n}$).

When $F = X\,G$ has no constant term in $X$, $\sum_m \mathrm{rowB}(m) x^m/m$ is
$\sum_{n \ge 1} \frac1n \sum_m W(m,n)\,([X^m]F^n)(y_n)\,x^m$, i.e. $\log\frac{1}{1 - tF}$ with
the monomial $x^m t^n$ replaced by $W(m,n)x^m$ and $Y$ by $y_n$. The general paper lemma (for
$H \in 1 + \mathbb Z[[x,y]]$ arbitrary, OEIS/A183241/README.md item 4) is more general than the
Lean, which only treats $H = 1/(1 - tF)$ with $F$ a polynomial.

**Theorem D** (power families; `DworkEuler.lean`). Let $f \in \mathbb Z[X]$, $f(0) = 1$, and
$U(m,n) = [x^m](x f)^n$. For $G : \mathbb N^2 \to \mathbb N$ put
$T(m,n) = \frac{m}{n}\,U(m,n)^{G(m,n)+1}$ (an integer, `Tpow`). If at the prime $p$, for all
$1 \le n \le m$,

- (mono) $G(m,n) \le G(pm,pn)$,
- (euler) $p^t \mid m,\ p^t \mid n \Rightarrow (p-1)p^t \mid G(pm,pn) - G(m,n)$,
- (big) $p \mid U(m,n) \ne 0 \Rightarrow \min\bigl(v_p(n),\, v_p(m)+1\bigr) \le G(m,n)$,

then $m \mapsto \sum_{n \le m} T(m,n)$ is Gauss at $p$ (`Tpow_gauss`). `gcond_of` derives these
conditions for $G(m,n) = g(n, m-n)$ ($n < m$), $G(m,m) = 0$, from:
$g(pn,pk) = g(n,k) + (p-1)L$ with $p^t \mid L$ whenever $p^t \mid n, k$; and
$\min(v_p(n), v_p(n+k)+1) \le g(n,k)$ whenever $p \mid U(n+k,n) \ne 0$.

**Theorem E** (partition sums; `DworkMultinomial.lean`). For $r \ge 1$,

$$P_r(n) = \sum_{\lambda \vdash n} \Bigl(\frac{n!}{\lambda_1!\,\lambda_2!\cdots}\Bigr)^{r}$$

is a Gauss sequence, so $\exp\bigl(\sum P_r(n)x^n/n\bigr) \in \mathbb Z[[x]]$. On the way, with
$\mathrm{mult}(\mu) = (\sum_i \mu_i)!/\prod_i \mu_i!$ for a multiset $\mu$ of naturals and
$p\mu$ the multiset of the $p\mu_i$: if $p^e \mid \sum\mu$ then
$p^{e+1} \mid \mathrm{mult}(p\mu) - \mathrm{mult}(\mu)$; if $\sum\mu = pn$, $p^e \mid n$ and some
$\mu_i$ is prime to $p$, then $p^{e+1} \mid \mathrm{mult}(\mu)$.

**Theorem F** (the $p$-local lemma; `DworkLocal.lean`). Fix a prime $p$ and let
$\mathbb Z_{(p)}$ be the rationals with denominator prime to $p$. Let $b : \mathbb N \to \mathbb Q$
with $b(n) \in \mathbb Z_{(p)}$ for $n \ge 1$ and $b(mp^a) - b(mp^{a-1}) \in p^a\mathbb Z_{(p)}$
for all $a \ge 1$, $m$. Then every $A_n(b) \in \mathbb Z_{(p)}$ (`expQ_pint_of_LGq`).
Perturbation (`expQ_perturb`): if $b \equiv b' \pmod{p^K}$ on $1, \dots, N$ with
$K \ge v_p(N!)$, $b'$ is $p$-integral there and $A_n(b')$ is $p$-integral for $n \le N$, then
$A_n(b) \equiv A_n(b') \pmod{p^{K - v_p(n!)}}$ and $A_n(b) \in \mathbb Z_{(p)}$ for $n \le N$.

## 2. When to reach for it

- The entry says "$\exp\bigl(\sum_{n\ge1} b(n)x^n/n\bigr)$ is an integer series" or
  "$a(n) = \frac1n\sum_{k=1}^n b(k)\,a(n-k)$ is always an integer": Theorem A.
- $b(n)$ is a sum of powers, products, subsequences of simpler Gauss sequences
  ($x^n$, $\binom{2n}{n}$, Lucas sequences, traces of integer matrices): Lemma B.
- $b(m) = \sum_{n \le m} (\text{weight}) \cdot \frac{m}{n}[x^m](\text{something})^n$, typically from
  $\exp\bigl(\sum_n A(x\cdot\ldots)^n x^n/n\bigr)$, $\exp\bigl(\sum_n (\sum_k B(n,k)^{e(n,k)}x^k)x^n/n\bigr)$
  or $(q^n + \ldots)^n$: Theorems C and D.
- $b(n)$ is a sum over partitions of $n$ of powers of multinomial coefficients: Theorem E.
- The series has rational coefficients with known denominators (e.g. $q^{-\binom n2}$, $1/2^n$) and
  the claim is integrality after rescaling: Theorem F, prime by prime, with a separate
  valuation bound at the primes in the denominator.
- Self-referential definitions $A(x) = \exp\bigl(\sum A(\ldots)^n x^n/n\bigr)$: `recSeq_int`
  reduces integrality to "for every integer truncation of $A$, the log-coefficients form a Gauss
  sequence".

## 3. Paper proof

The equivalence of Gauss congruences with integrality of $\exp\bigl(\sum b(n)x^n/n\bigr)$ goes back
to B. Dwork, *Norm residue symbol in local number fields*, Abh. Math. Sem. Univ. Hamburg 22 (1958)
(the $p$-adic form is the Dieudonné–Dwork lemma); the Euler-product form is classical. The lifted
Frobenius congruence for coefficients of powers is the usual
tool for constant terms of powers of Laurent polynomials. The packaging into Theorems C and D
(ray congruences, power families with the conditions mono/euler/big), Theorem E's route via
the multinomial Frobenius congruence, and all Lean proofs were written for this repository.

### Theorem A

*(2 ⇒ 3).* Each factor $(1-x^d)^{-c}$, $c \in \mathbb Z$, lies in $\mathbb Z[[x]]$ (a polynomial if
$c \le 0$, a power of $1 + x^d + x^{2d} + \cdots$ if $c > 0$), so the product
$P = \prod_{d \ge 1}(1-x^d)^{-c(d)}$ does (only $d \le n$ matters for $[x^n]$). Its logarithmic
derivative is

$$\frac{xP'}{P} = \sum_{d} c(d)\,\frac{d\,x^d}{1 - x^d} = \sum_{n\ge1}\Bigl(\sum_{d\mid n} d\,c(d)\Bigr)x^n
= \sum_{n \ge 1} b(n)x^n.$$

With $P(0) = 1$, the coefficients of $P$ satisfy the recurrence defining $A_n$, which has a unique
solution, so $A_n = [x^n]P \in \mathbb Z$.

*(2 ⇒ 1).* $d \mid mp^a$ but $d \nmid mp^{a-1}$ exactly when $v_p(d) = v_p(m) + a$, so
$b(mp^a) - b(mp^{a-1}) = \sum d\,c(d)$ over such $d$, and $p^a$ divides every such $d$.

*(1 ⇒ 2).* Define $c(n) \in \mathbb Q$ by the recursion in Theorem A; then
$b(n) = \sum_{d \mid n} d\,c(d)$ by construction, and we show $c(n) \in \mathbb Z$ by strong
induction. Let $p$ be a prime, $a = v_p(n) \ge 1$. Subtracting the identities for $n$ and $n/p$,

$$b(n) - b(n/p) = \sum_{d \mid n,\ v_p(d) = a} d\,c(d) = n\,c(n) + \sum_{d \mid n,\ v_p(d) = a,\ d < n} d\,c(d).$$

The left side is divisible by $p^a$ (Gauss congruence with $m = n/p^a$), and every term of the
last sum is an integer divisible by $p^a$ (induction). So $p^{v_p(n)}$ divides the integer
$n\,c(n) = b(n) - \sum_{d \mid n, d<n} d\,c(d)$ for every $p \mid n$, hence $n \mid n\,c(n)$ and
$c(n) \in \mathbb Z$.

*(3 ⇒ 2).* Again define $c$ by the recursion; suppose $c(d) \in \mathbb Z$ for $d < n$. Then
$P_{n-1} = \prod_{d<n}(1-x^d)^{-c(d)} \in 1 + x\mathbb Z[[x]]$ is invertible in $\mathbb Z[[x]]$,
and in $\mathbb Q[[x]]$

$$\frac{E}{P_{n-1}} = \exp\Bigl(\sum_{k \ge 1}\Bigl(b(k) - \sum_{d \mid k,\ d < n} d\,c(d)\Bigr)\frac{x^k}{k}\Bigr)
= \exp\bigl(c(n)x^n + O(x^{n+1})\bigr) = 1 + c(n)x^n + O(x^{n+1}),$$

because the bracket vanishes for $k < n$ and equals $n\,c(n)$ for $k = n$. The left side lies
in $\mathbb Z[[x]]$, so $c(n) \in \mathbb Z$.

### Lemma B

Sums, negation and constants are immediate. Products: with $N = mp^a$, $M = mp^{a-1}$,
$f(N)g(N) - f(M)g(M) = f(N)\bigl(g(N) - g(M)\bigr) + g(M)\bigl(f(N) - f(M)\bigr)$; powers by
induction. Subsequences: apply the congruence for $f$ with $m$ replaced by $mk$.

*Fermat–Euler* (`pow_gauss`): for $x \in \mathbb Z$, $t \ge 1$, $a \ge 1$,
$p^a \mid x^{tp^a} - x^{tp^{a-1}}$. If $p \mid x$, both terms are divisible by
$p^{tp^{a-1}}$ and $tp^{a-1} \ge p^{a-1} \ge a$. If $p \nmid x$, Euler's theorem with
$\varphi(p^a) = p^{a-1}(p-1) \mid tp^a - tp^{a-1}$ gives it. This is the statement that
$j \mapsto x^j$ is Gauss.

*$j \mapsto f(j)^{jc}$*: write $N = mp^a$, $M = mp^{a-1}$ and split
$f(N)^{Nc} - f(M)^{Mc} = \bigl(f(N)^{Nc} - f(M)^{Nc}\bigr) + \bigl(f(M)^{Nc} - f(M)^{Mc}\bigr)$.
The first bracket is divisible by $f(N) - f(M)$, hence by $p^a$; the second by Fermat–Euler
with $t = mc$. `W1_pow` in Theorem C is the same computation with $\kappa$ in place of $jc$.

### Theorem C

*(a) Lifted Frobenius.* In $\mathbb F_p[Y][X]$ the $p$-th power map is a ring endomorphism fixing
$\mathbb F_p$, so $F^p \equiv \phi(F) \pmod p$ where $\phi$ substitutes $X \mapsto X^p$,
$Y \mapsto Y^p$. If $A \equiv B \pmod{p^{j}}$ with $j \ge 1$ then $A^p \equiv B^p \pmod{p^{j+1}}$
(binomial expansion), so $F^{p\cdot p^e} \equiv \phi(F)^{p^e} \pmod{p^{e+1}}$ and, raising to a
$t$-th power, $F^{pk} \equiv \phi(F^k) \pmod{p^{e+1}}$ whenever $p^e \mid k$ (`frob_pow_congr`).
Taking the coefficient of $X^{pm}$: $[X^{pm}]F^{pn} \equiv \bigl([X^m]F^n\bigr)(Y^p)
\pmod{p^{e+1}}$ when $p^e \mid n$ (`coeff_frob_congr`), and $[X^{i}]F^{pn} \equiv 0$ when
$p \nmid i$.

*(b) $p^e \mid n \Rightarrow p^e \mid m\,[X^m]F^n$* (`dvd_m_mul_coeff`), by induction on $e$.
For $e \ge 1$ write $n = pn'$ with $p^{e-1} \mid n'$. By (a), $[X^m]F^n \equiv 0
\pmod{p^e}$ if $p \nmid m$, and if $m = pm'$ then
$m[X^m]F^n \equiv p\,m'\,\bigl([X^{m'}]F^{n'}\bigr)(Y^p) \pmod{p^e}$, where
$m'[X^{m'}]F^{n'}$ is divisible by $p^{e-1}$ by induction. Applying (b) to each prime power in
$n$ shows $n \mid m\,[X^m]F^n$, so $V(m,n) \in \mathbb Z$.

*(c) `V0`: $p^k \mid m$, $p^{s+1} \nmid n \Rightarrow p^{k-s} \mid V(m,n)$* (with $k - s$
truncated at $0$). From $n\,V = m\cdot([X^m]F^n)(y_n)$ the right side has $v_p \ge k$ and
$v_p(n) \le s$.

*(d) `V1`: $p^k \mid m \Rightarrow p^{k+1} \mid V(pm,pn) - V(m,n)$.* Let $e = v_p(n)$ and
$Q = [X^m]F^n \in \mathbb Z[Y]$. Then

$$n\bigl(V(pm,pn) - V(m,n)\bigr) = m\Bigl(\bigl([X^{pm}]F^{pn}\bigr)(y_{pn}) - Q(y_n)\Bigr).$$

By (a), $([X^{pm}]F^{pn})(y_{pn}) \equiv Q(y_{pn}^{\,p}) \pmod{p^{e+1}}$, and
$y_{pn}^{\,p} \equiv y_n \pmod{p^{e+1}}$ (admissibility) gives $Q(y_{pn}^{\,p}) \equiv Q(y_n)$.
So the right side is divisible by $p^{k+e+1}$; divide by $n$.

*(e) Row sums* (`rowsum_gauss`). Let $T(m,n)$ satisfy (T0) $p^k \mid m$, $p \nmid n \Rightarrow
p^k \mid T(m,n)$ and (T1) $p^k \mid m \Rightarrow p^{k+1} \mid T(pm,pn) - T(m,n)$. Then
$R(m) = \sum_{n\le m} T(m,n)$ is Gauss at $p$: in $R(Mp^a)$ the terms with $p \nmid n$ are
$\equiv 0 \pmod{p^a}$ by (T0), and the terms $n = pn'$, $n' \le Mp^{a-1}$, satisfy
$T(p\cdot Mp^{a-1}, pn') \equiv T(Mp^{a-1}, n') \pmod{p^a}$ by (T1) with $k = a-1$; their sum is
$R(Mp^{a-1})$.

*(f) Conclusion* (`rowB_gauss`). Take $T = W\,V$. (T0) is (c) with $s = 0$. For (T1) write
$W'V' - WV = W'(V' - V) + V(W' - W)$ with primes denoting the arguments $(pm,pn)$. The first
term is handled by (d). If $p^k \mid n$, the ray congruence gives $p^{k+1} \mid W' - W$.
Otherwise $t = v_p(n) < k$; (c) with $s = t$ gives $p^{k-t} \mid V$ and the ray congruence at
level $t$ gives $p^{t+1} \mid W' - W$. Theorem A finishes.

*Admissible points.* $y_n = 0$ is trivial. For $y_n = q^n$ and $n = p^e t$:
$y_{pn}^{\,p} - y_n = q^{tp^{e+2}} - q^{tp^e} = (q^{tp^{e+2}} - q^{tp^{e+1}}) + (q^{tp^{e+1}} - q^{tp^e})$,
both divisible by $p^{e+1}$ by Fermat–Euler.

### Theorem D

$T(m,n) = V(m,n)\,U(m,n)^{G(m,n)}$ with $V(m,n) = \frac mn U(m,n)$, which is Theorem C's $V$ for
$F = xf$, $y \equiv 0$. (T0) is (c). For (T1), write $U' = U(pm,pn)$, $G' = G(pm,pn)$ and
$T' - T = U'^{G'}(V' - V) + V\,(U'^{G'} - U^{G})$; the first term is (d). Let $s = v_p(n)$,
$k \le v_p(m)$. By (a), $U' \equiv U \pmod{p^{\tau+1}}$ for every $\tau \le s$.

- $U = 0$: then $V = 0$.
- $p \mid U \ne 0$: then $p \mid U'$ and, since $G \le G'$, $p^{G} \mid U'^{G'} - U^G$. If
  $s \le k$, then $p^{k+1} \mid nV = mU$ gives $p^{k+1-s} \mid V$, and (big) gives
  $G \ge \min(s, v_p(m)+1) = s$. If $s > k$, (big) gives $G \ge k+1$.
- $p \nmid U$: put $\tau = \min(k,s)$. By (euler), $G' - G = (p-1)p^{\tau}d$, and
  $U^{(p-1)p^\tau} \equiv 1 \pmod{p^{\tau+1}}$ (Euler). Hence
  $U'^{G'} - U^G = (U'^{G'} - U^{G'}) + U^G(U^{G'-G} - 1) \equiv 0 \pmod{p^{\tau+1}}$, and
  $p^{k-\tau} \mid V$ by (c).

In every case $p^{k+1} \mid V(U'^{G'} - U^G)$, and (e) applies.

### Theorem E

Let $P = x_0 + \cdots + x_{K-1} \in \mathbb Z[x_0, \dots]$. As in (a), $P^{pk} \equiv
\mathrm{expand}_p(P^k) \pmod{p^{e+1}}$ when $p^e \mid k$, where $\mathrm{expand}_p$ substitutes
$x_i \mapsto x_i^p$. The coefficient of $x^{p\mu}$ on the left is $\mathrm{mult}(p\mu)$, on the right
$\mathrm{mult}(\mu)$; the coefficient of a monomial with an exponent
prime to $p$ is $0$ on the right. This gives both multinomial congruences.

For the Gauss congruence of $P_r$ at $(a, m)$ put $n = mp^{a-1}$. Partitions of $pn$ with all
parts divisible by $p$ are exactly $p\lambda$ for $\lambda \vdash n$, and
$\mathrm{mult}(p\lambda)^r \equiv \mathrm{mult}(\lambda)^r \pmod{p^a}$ (congruence with $e = a-1$, then
powers). Every other partition of $pn$ has a part prime to $p$, so its multinomial, and hence
its $r$-th power ($r \ge 1$), is divisible by $p^a$. So $P_r(pn) \equiv P_r(n) \pmod{p^a}$.

### Theorem F

*Exponents are $p$-integral* (`cQ_pint`). Define $c(n) \in \mathbb Q$ by the recursion of
Theorem A. The proof of (1 ⇒ 2) above, run in $\mathbb Z_{(p)}$ at the single prime $p$, shows
$p^{v_p(n)} \mid n\,c(n)$ in $\mathbb Z_{(p)}$; the prime-to-$p$ part of $n$ is a unit, so
$c(n) \in \mathbb Z_{(p)}$.

*Perturbation* (`expQ_perturb`), by induction on $n$: with $A = A(b)$, $A' = A(b')$,

$$(n+1)(A_{n+1} - A'_{n+1}) = \sum_{j \le n}\Bigl(b(j+1)\,(A_{n-j} - A'_{n-j}) + \bigl(b(j+1) - b'(j+1)\bigr)A'_{n-j}\Bigr).$$

Each term has $v_p \ge K - v_p((n-j)!) \ge K - v_p(n!)$, and dividing by $n+1$ costs
$v_p(n+1)$, giving $v_p(A_{n+1} - A'_{n+1}) \ge K - v_p((n+1)!) \ge 0$.

*Conclusion* (`expQ_pint_of_LGq`). Fix $n$, $K = v_p(n!)$. Choose integers $c'(d) \equiv c(d)
\pmod{p^K}$ (`approx`) and put $b'(k) = \sum_{d \mid k} d\,c'(d)$. Then $b' \equiv b
\pmod{p^K}$, $A(b')$ is integral by Theorem A, and the perturbation lemma gives $A_n(b) \in
\mathbb Z_{(p)}$. This route (integer approximation plus Theorem A) replaces the classical
$p$-adic proof of Dieudonné–Dwork.

## 4. Worked example: A183129 (and its eight siblings)

**Claim** ([A183129](https://oeis.org/A183129), P. D. Hanna 2011). The coefficients of

$$A(x) = \exp\Bigl(\sum_{n \ge 1}\Bigl[\sum_{k \ge 0}\binom{n+k-1}{k}^{k^2+k} x^k\Bigr]\frac{x^n}{n}\Bigr)$$

are integers: 1, 1, 2, 5, 374, 8404542, 48017057808567, ... ("Conjecture" in the entry).

**Reduction.** Collect $x^m$: $A = \exp\bigl(\sum_m b(m)x^m/m\bigr)$ with

$$b(m) = \sum_{n=1}^{m}\frac{m}{n}\binom{m-1}{m-n}^{e(n,\,m-n)}, \qquad e(n,k) = k^2 + k \ (k \ge 1),\quad e(n,0) = 1.$$

With $f = 1 + x + \cdots + x^N$ ($N$ at least the target degree),
$U(m,n) = [x^m](xf)^n = \binom{m-1}{m-n}$ for $1 \le n \le m \le N$ (`U_geom`), so
$b(m) = \sum_n T(m,n)$ is the row sum of the power family of Theorem D with $G = e - 1$
($G = 0$ on the diagonal). The `gcond_of` inputs, with $g(n,k) = k^2 + k - 1$:

- $g(pn,pk) - g(n,k) = (p^2-1)k^2 + (p-1)k = (p-1)L$ with $L = (p+1)k^2 + k$, and
  $p^t \mid k \Rightarrow p^t \mid L$;
- with $\mu = \min(v_p(n+k), v_p(n))$, $p^\mu \mid k$, so
  $\min(v_p(n), v_p(n+k)+1) \le \mu + 1 \le p^\mu \le k \le g(n,k)$ (`big_k`).

So $b$ is a Gauss sequence and Theorem A gives integrality.

**Small case.** $b(1), \dots, b(4)$:

| $m$ | terms $\frac mn\binom{m-1}{m-n}^{e}$, $n = m, m-1, \dots, 1$ | $b(m)$ |
|---|---|---|
| 1 | $1$ | 1 |
| 2 | $1 + 2\cdot 1^{2}$ | 3 |
| 3 | $1 + \frac32\cdot 2^{2} + 3\cdot 1^{6}$ | 10 |
| 4 | $1 + \frac43\cdot 3^{2} + 2\cdot 3^{6} + 4\cdot 1^{12}$ | 1475 |

Gauss congruences: $b(2) - b(1) = 2$, $b(4) - b(2) = 1472 = 4\cdot 368$, $b(3) - b(1) = 9$.
Recurrence: $A_1 = 1$, $2A_2 = 1 + 3 = 4$, $3A_3 = 2 + 3 + 10 = 15$,
$4A_4 = 5 + 6 + 10 + 1475 = 1496$, so $A = 1, 1, 2, 5, 374$. Dwork exponents:
$c(1) = 1$, $c(2) = (3-1)/2 = 1$, $c(3) = (10-1)/3 = 3$, $c(4) = (1475 - 1 - 2)/4 = 368$, and
$(1-x)^{-1}(1-x^2)^{-1}(1-x^3)^{-3}(1-x^4)^{-368} = 1 + x + 2x^2 + 5x^3 + 374x^4 + O(x^5)$.

**Lean.** `A183129.A183129_int : ∀ N, ∃ z : ℤ, a183129 N = z` in
[`OEIS/A183129/A183129_mathlib.lean`](../../OEIS/A183129/A183129_mathlib.lean), via `fam2_int`
($f$ = `geomTrunc N`, `U_geom`), `Tpow_gauss`, `gcond_of`, `recSeq_int`. The same file proves
A181070, A181074, A181076, A181078, A181080, A181082, A181084, A183128 ($B = \binom nk$ uses
$f = 1 + x$, `U_one_add_X`).

### Second example: the $p$-local version, A176827

**Claim** ([A176827](https://oeis.org/A176827)). With $A(x) = \exp\bigl(\sum_{n\ge1}
A(x/q^n)^n x^n/n\bigr)$ and $a(n) = q^{\binom n2}[x^n]A$, every $a(n)$ is an integer for every
integer $q \ge 1$. For $q = 3$: $A_N = 1, 1, \frac43, \frac{43}{27}, \frac{1288}{729}, \dots$ and
$a(n) = 1, 1, 4, 43, 1288, 111874, \dots$ (the entry's data).

**Route.** Prime by prime. At $p \mid q$ a direct valuation bound $v_p(A_N) \ge
-v_p(q)\binom N2$ (for $q = 3$: $v_3(43/27) = -3 = -\binom32$, $v_3(1288/729) = -6 =
-\binom42$). At $p \nmid q$, induction on $N$: approximate $1/q$ by an integer $Q$ and
$A_0, \dots, A_{N-1}$ by integers modulo $p^{K}$, $K = v_p(N!) + N$. The integer model
$\exp\bigl(\sum_n A'(Q^n x)^n x^n/n\bigr)$, whose log-coefficients are $\mathrm{rowB}$ of Theorem C with
$F = X\cdot A'$ (truncated), $y \equiv 0$, $W(m,n) = Q^{n(m-n)}$ (`W1_pow` with $u(n) = Q^n$,
$\kappa = m - n$), is integral (`rowB_int`); its log-coefficients agree with those of $A$ modulo
$p^K$, and `expQ_perturb` transfers $p$-integrality to $A_N$. For $q = 3$, $p = 2$:
$A_2 = 4/3$, $A_3 = 43/27$ are $2$-integral as required.

**Lean.** `A176827.A176827_int (q n : ℕ) (hq : 1 ≤ q) : ∃ z : ℤ, a q n = z` in
[`OEIS/A176827/A176827_mathlib.lean`](../../OEIS/A176827/A176827_mathlib.lean); the valuation
bookkeeping uses `Wt`, `CP`, `PV_pow_sub`, `expQ_eq_of_rec` from `DworkLocalPoly.lean`.

## 5. In Lean

Series are never formed as `exp`/`log` of power series; everything is the coefficient recurrence.

**`OpenProblemsLib.Dwork`** (`import OpenProblemsLib.Dwork`)

| declaration | meaning |
|---|---|
| `expCoeff b n` | $A_n(b)$ over $\mathbb Q$ by the recurrence |
| `LGp p b` | Gauss congruences at $p$ |
| `cOf b n` | Dwork exponents $c(n)$ (integer division) |
| `dwork` | Gauss at every prime ⇒ $b(n) = \sum_{d\mid n} d\,c(d)$ |
| `LGp_of_euler` | Euler form ⇒ Gauss at every prime |
| `expCoeff_int_of_euler` | Euler form ⇒ $A_n \in \mathbb Z$ |
| `expCoeff_int_of_gauss` | Gauss at every prime ⇒ $A_n \in \mathbb Z$ |
| `euler_of_expCoeff_int`, `gauss_of_expCoeff_int` | $A_n \in \mathbb Z$ ⇒ Euler form, Gauss |
| `LGp_add`, `LGp_neg`, `LGp_sub`, `LGp_const`, `LGp_mul`, `LGp_pow`, `LGp_sum`, `LGp_comp_mul`, `LGp_zpow`, `LGp_pow_self` | Lemma B |
| `pow_gauss`, `fermat_int` | Fermat–Euler $p^a \mid x^{tp^a} - x^{tp^{a-1}}$; Fermat |
| `expCoeff_congr`, `eq_expCoeff_of_rec` | $A_n$ depends only on $b(1..n)$; any solution of the recurrence is `expCoeff` |

**`OpenProblemsLib.DworkEuler`** (`import OpenProblemsLib.DworkEuler`)

| declaration | meaning |
|---|---|
| `frobLift`, `frob_pow_congr`, `coeff_frob_congr` | step (a) |
| `dvd_m_mul_coeff`, `V`, `V_mul`, `V0`, `V1` | steps (b)–(d) |
| `YCond`, `ycond_zero`, `ycond_pow` | admissible points $0$, $q^n$ |
| `W1`, `W1_one`, `W1_pow` | ray congruences of the weights |
| `rowsum_gauss` | step (e) |
| `rowB`, `rowB_gauss`, `rowB_int` | Theorem C |
| `U`, `Tpow`, `GCond`, `Tpow_gauss`, `gcond_of` | Theorem D |
| `U_one_add_X`, `U_geom`, `geomTrunc`, `U_diag` | $U$ for $f = 1+x$ and $f = 1 + \cdots + x^N$ |
| `recSeq bf`, `Local`, `recSeq_rec`, `recSeq_int` | self-referential series: integral if every integer truncation gives a Gauss log-sequence |
| `gpoly`, `coeff_X_mul_gpoly_pow`, `V_cast_eval` | glue between $V$ and truncations of $A$ |

**`OpenProblemsLib.DworkMultinomial`**: `multinomial_smul_congr`, `multinomial_dvd_of_not_dvd`,
`partitionSum r n`, `LGp_partitionSum`, `expCoeff_partitionSum_int` (Theorem E).

**`OpenProblemsLib.DworkLocal`**: `PV p k x` ($v_p(x) \ge k$, $k \in \mathbb Z$) and its closure
lemmas; `approx`; `int_of_PV`; `expQ b n` ($A_n$ for $b : \mathbb N \to \mathbb Q$),
`expQ_cast`; `expQ_perturb`; `LGq`, `cQ`, `cQ_pint`, `expQ_pint_of_LGq` (Theorem F).

**`OpenProblemsLib.DworkLocalPoly`** (declarations in namespace `OpenProblemsLib.DworkLocal`):
`Wt p v f` ($v_p([x^i]f) \ge -v\binom i2$, closed under products), `CP p k f` (coefficientwise
$p^k \mid f$) with `CP_pow_sub`, `PV_pow_sub`, `PV_qpow`, `choose_two_add`, `expQ_eq_of_rec`.

**Problems using it** (import found by grep, 2026-11-06):

- `Dwork`: [A181316](../../OEIS/A181316/), [A177430](../../OEIS/A177430/),
  [A183241/A165940](../../OEIS/A183241/A165940_mathlib.lean).
- `DworkEuler`: [A183129 group](../../OEIS/A183129/), [A163138](../../OEIS/A163138/),
  [A163921](../../OEIS/A163921/), [A183241/A156907](../../OEIS/A183241/A156907_mathlib.lean),
  [A183241/A157675](../../OEIS/A183241/A157675_mathlib.lean), [A176827](../../OEIS/A176827/).
- `DworkMultinomial`: [A183241, A182963](../../OEIS/A183241/A183241_mathlib.lean).
- `DworkLocal`: A177430, A183241/A165940 (`expQ_pint_of_LGq`), A176827 (`expQ_perturb`).
- `DworkLocalPoly`: A176827.
- Local copies of `Dwork.lean` material not yet switched to the import (see
  `lib/DUPLICATES.md`): A158110, A183241/A174470, A207969, A208034.
- `lib/test/DworkAxioms.lean` prints the axioms of the main theorems.
