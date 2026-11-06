\\ A214724: a(n) = n! [x^n] exp(sum_k x^(k^2+1)/(k^2+1)); check p | a(n), p <= n <= N,
\\ for the primes p = m^2+1 <= N, and agreement with the b-file values read from b.
N = 449;
A = Vec(serlaplace(exp(sum(k=0, 30, x^(k^2+1)/(k^2+1)) + O(x^(N+1)))));
bad = 0;
forstep(m = 1, 30, 1, p = m^2 + 1; if(p <= N && isprime(p), for(n = p, N, if(A[n+1] % p, bad++; print("fail ", p, " ", n)))));
print("divisibility failures: ", bad);
