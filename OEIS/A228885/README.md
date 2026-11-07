# OEIS A228885: sign of det[[gcd(i+j, n) = 1]] for squarefree n

**Source.** [A228885](https://oeis.org/A228885), Zhi-Wei Sun (Sep 2013): a(n) = det of the n X n matrix with
(i,j)-entry 1 or 0 according as i+j is coprime to n or not. "Conjecture: If n is squarefree, then
(-1)^(n*(n-1)/2)*a(n) > 0." Ridouane Oudra (Mar 2025) conjectured
a(n) = (-1)^floor(n/2) mu(n)^2 Prod_{d|n} phi(d)^{phi(n/d)}. (OEIS text, CC BY-SA 4.0, cached entry read
2026-11-07.)

**Reading.** Indices 1..n or 0..n-1 give the same determinant: shifting i by 2 permutes rows cyclically by an
even permutation of sign (-1)^{2(n-1)} = 1.

**Result.** Both conjectures are true: a(n) = (-1)^floor(n/2) Prod_{d|n} phi(d)^{phi(n/d)} for squarefree n, and
a(n) = 0 otherwise (the entry already proves the zero case).

**Argument.** Let g(m) = [gcd(m,n) = 1] and P the permutation matrix of j -> -j mod n. Then M P is the circulant
with entries g(i-j), whose eigenvalues are the Ramanujan sums c_n(k) = mu(n/d) phi(n)/phi(n/d), d = gcd(n,k).
So a(n) = det(P) Prod_{k=0}^{n-1} c_n(k). The involution j -> -j fixes 0 (and n/2 for even n), so
det P = (-1)^floor((n-1)/2). For squarefree n every mu(n/d) is +-1. The number of k with n/gcd(n,k) = e is phi(e),
so the sign of the product is Prod_{e|n} mu(e)^{phi(e)}; phi(e) is even for e > 2, so only e = 2 can contribute,
and the sign is -1 iff n is even. Hence sign a(n) = (-1)^floor((n-1)/2) for odd n and -(+1) = -1 for even
squarefree n (n = 2 mod 4, floor((n-1)/2) even). In both cases this is (-1)^{n(n-1)/2} = (-1)^floor(n/2).
Absolute value: Prod_{e|n} (phi(n)/phi(e))^{phi(e)} = Prod_{e|n} phi(n/e)^{phi(e)} (phi multiplicative,
n squarefree), which is Oudra's product.

**Evidence.** [`certificate/check.py`](certificate/check.py): the Ramanujan-sum product equals the determinant
for n = 1..30 (exact sympy). Lean: none (needs Mathlib: circulant determinant via characters, Ramanujan sums).
Outside Lean: the argument above (standard circulant diagonalisation and von Sterneck's formula for c_n(k)).

**Review level.** `rechecked`.

**Prior art.** Checked 2026-11-07. The entry proves a(n) = 0 for non-squarefree n, phi(n) | a(n) and a(p); Oudra's
formula is labelled a conjecture. Web search found no proof. Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs. New but immediate.
