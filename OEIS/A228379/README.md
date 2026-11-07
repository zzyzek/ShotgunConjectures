# OEIS A228379: sign and divisibility of |(i^2+j^2)^n|_{0<=i,j<=n-1}

**Source.** [A228379](https://oeis.org/A228379), Zhi-Wei Sun (2013): a(n) = det[(i^2+j^2)^n]_{0<=i,j<=n-1}.
"Conjecture: If n > 2, then (-1)^{n(n-1)/2}*a(n) > 0 and 2*Product_{k=1..n} (k!*(2k-1)!) divides a(n)."
(OEIS text, CC BY-SA 4.0, cached entry read 2026-11-07.)

**Result.** True; proved by Grinberg, Sun and Zhao, "Proof of three conjectures on determinants related to
quadratic residues", Linear Multilinear Algebra (arXiv:2007.06453), Theorem 1.2 (with d = 1): b'_n =
b_n / (2 Prod_{k=1}^n k!(2k-1)!) is an integer and (-1)^{n(n-1)/2} b_n > 0 for n > 2. The entry links this paper
but still labels the comment a conjecture. The companion conjecture on det[(i+j)^n] in the same entry is the
a'_n part of the same theorem (c = 0, d = 1).

**Argument (re-derived).** (i^2+j^2)^n = Sum_k C(n,k) x_i^k y_j^{n-k} with x_i = y_i = i^2. Cauchy-Binet over the
n-subsets of {0..n} (GSZ Theorem 3.1) gives
a(n) = (-1)^{n(n-1)/2} V^2 S, V = Prod_{0<=i<j<n} (j^2 - i^2), S = Sum_m e_m(x) e_{n-m}(x) Prod_{k != m} C(n,k),
with e_m the elementary symmetric functions of x_0..x_{n-1}. Since x_0 = 0 and the other x_i > 0, the terms
m = 0, n vanish and the terms 1 <= m <= n-1 are positive, so (-1)^{n(n-1)/2} a(n) > 0 for n >= 2.
Divisibility: V = Prod_{j=1}^{n-1} j (2j-1)!, and K(n) = V^2 (2n-1) / (2 Prod k!(2k-1)!) satisfies
K(n)/K(n-1) = (2n-4)!/(2n (n-2)!), an integer for n >= 5, with K(6) an integer; when p = 2n-1 is prime,
the nonzero x_i are the quadratic residues mod p, so Prod (t - x_i) = t^{n-1} - 1 mod p, e_m = 0 mod p for
1 <= m <= n-2, and p | S. (For composite 2n-1 the extra prime powers come from V^2; this part is GSZ's.)

**Evidence.** [`certificate/check.py`](certificate/check.py) checks the Cauchy-Binet formula against the
determinant for n <= 9; [`certificate/check2.py`](certificate/check2.py) checks the divisibility for n <= 60 and
p | S for prime p = 2n-1. Lean: none. Outside Lean: Grinberg-Sun-Zhao Theorem 1.2.

**Review level.** `rechecked`.

**Prior art.** Checked 2026-11-07: GSZ arXiv:2007.06453v2, Theorem 1.2 read (pdftotext). Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
