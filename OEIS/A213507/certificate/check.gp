\\ A213507: e.g.f. exp(sum Catalan(n) x^n/n). Checks
\\ (1) the e.g.f. equals C(x)^2 exp(-x C(x)^2) (Bala) to O(x^N);
\\ (2) the Bala congruence a(n+k) = (-1)^k a(n) (mod k) for n + k < N;
\\ (3) for each listed prime p, a(n) mod p != 0 for 0 <= n < 2p (the period divides 2p by (2)).
N = 400;
L = sum(m=1, N, binomial(2*m,m)/(m+1)*x^m/m) + O(x^(N+1));
A = exp(L);
C = (1 - sqrt(1 - 4*x + O(x^(N+2))))/(2*x);
B = C^2*exp(-x*C^2);
print("egf identity: ", A == B + O(x^(N+1)));
a = vector(N, n, polcoeff(A, n-1)*(n-1)!);   \\ a[n+1] = a(n)
print("first terms: ", a[1..11]);
bad = 0; for(n=0, N-2, for(k=1, N-1-n, if((a[n+k+1] - (-1)^k*a[n+1]) % k != 0, bad++))); print("congruence failures: ", bad);
P = [2,5,13,29,31,37,41,43,53,71,97];
for(i=1, #P, p = P[i]; z = sum(n=0, 2*p-1, a[n+1] % p == 0); per = vector(2*p, n, a[n] % p) == vector(2*p, n, a[n+2*p] % p); print(p, ": zeros in a(0..2p-1) mod p = ", z, ", period 2p seen = ", per));
