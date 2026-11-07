# OEIS A228884: det[gcd(i-j, n)] is positive, divisible by phi(n)^phi(n) Sum_{d|n} phi(d) n/d, with small prime factors

**Source.** [A228884](https://oeis.org/A228884), Zhi-Wei Sun (Sep 2013): a(n) = det[gcd(i-j, n)]_{0<=i,j<=n-1}.
"Conjecture: (i) a(n) is always positive and divisible by Phi(n)^{Phi(n)}*sum_{d|n}Phi(d)*n/d ... (ii) For any
composite number n, all prime divisors of a(n) are smaller than n." (OEIS text, CC BY-SA 4.0, cached entry read
2026-11-07.)

**Result.** Both parts are true, with the closed form
a(n) = Prod_{k=0}^{n-1} lambda(gcd(k,n)),  lambda(g) = Sum_{e | g} e phi(n/e)
     = Prod_{p^a || n} [ (b+1) p^{a-1}(p-1) if b < a ;  p^{a-1}((a+1)p - a) if b = a ],  p^b || g.

**Argument.** The matrix is circulant (entry depends on i-j mod n), so its eigenvalues are
lambda_k = Sum_{m=0}^{n-1} gcd(m,n) w^{mk}, w = e^{2 pi i/n}, and a(n) = Prod_k lambda_k. Writing
gcd(m,n) = Sum_{d | gcd(m,n)} phi(d) and summing the geometric series over m in dZ/nZ,
lambda_k = Sum_{d|n, (n/d)|k} phi(d) n/d = Sum_{e | gcd(k,n)} e phi(n/e),
a positive integer; this is multiplicative in (n, gcd(k,n)), giving the local factors above
(for b < a every phi(p^{a-c}) equals p^{a-c-1}(p-1); for b = a the term c = a adds p^a).
(i) Every factor is positive. lambda_0 = Sum_{d|n} phi(d) n/d. For the phi(n) values of k coprime to n (n >= 2),
lambda_k = phi(n). So a(n) = lambda_0 phi(n)^{phi(n)} times a product of integers (n = 1: a(1) = 1).
(ii) The primes dividing the local factors divide p, p-1, b+1 <= a, or (a+1)p - a. All are below n when n is
composite: p < n; b+1 <= a < n; if n = p^a with a >= 2 then (a+1)p - a <= p^a (equality only at p = 2, a = 2,
where the factor is 4 = 2^2); if n has another prime factor then (a+1)p - a < 2p^a <= n.

**Evidence.** [`certificate/check.py`](certificate/check.py): the product formula equals the determinant for
n = 1..30 (exact sympy). Lean: none (needs Mathlib: circulant determinant as a product over characters).
Outside Lean: the argument above (the circulant eigenvalue formula is standard).

**Review level.** `rechecked`.

**Prior art.** Checked 2026-11-07. The entry notes the divisibility by Sum_{d|n} phi(d) n/d and a(p) for primes
(both special cases of the formula) and nothing else. Web search found no proof; the related determinant of
Ramanujan sums over divisors (Q1984243) is a different matrix. Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs (local clones, 2026-11-06). The method (circulant diagonalisation) is classical, so
the result is new but immediate.
