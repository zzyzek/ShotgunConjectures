\\ a(n) with prime factors <= n: for n = 55 enumerate all subsets of primes <= 55;
\\ for n = 6543 (prime(n) = 65537) find s = product of 17 distinct primes <= 65537 with s+1 prime and s > every 16-prime product.
P = primes([2, 55]); best = 0; bests = 0;
forvec(v = vector(#P, i, [0, 1]), s = prod(i = 1, #P, if (v[i], P[i], 1)); if (s + 1 > best && ispseudoprime(s + 1), best = s + 1; bests = s));
print("a(55) = ", best, " omega(a-1) = ", omega(best - 1), " need 8 (tau = 256)");
print("primepi(55) = ", primepi(55), " prime(55) = ", prime(55), " prime(6543) = ", prime(6543));
Q = primes([2, 65537]); top16 = prod(i = #Q - 15, #Q, Q[i]);
setrand(1); found = 0;
for (tries = 1, 100000, pm = numtoperm(40, random(40!)); S = vector(17, i, Q[#Q - 40 + pm[i]]); t = 2 * prod(i = 1, 17, S[i]); if (t > top16 && ispseudoprime(t + 1), print("18-prime witness 2 times: ", S, " t > top16: ", t > top16); found = 1; break));
print("found = ", found);
