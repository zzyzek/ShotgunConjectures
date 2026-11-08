\\ Extended PRP search b in (5000, BMAX] for odd n with no representation found for b <= 5000.
\\ Small factors screened by gcd with the product of primes < 10^5.
n = eval(getenv("N")); BMAX = eval(getenv("BMAX"));
Q = prod(i=1, primepi(10^5), prime(i)) / 2;
{for(b=5001, BMAX,
  t = 2^b;
  foreach([t - n, t + n], v,
    if(gcd(v, Q) == 1 && ispseudoprime(v), print(n, " b=", b, " ", if(v == t - n, "2^b-n", "2^b+n"), " PRP digits ", #Str(v)); quit));
  if(b % 1000 == 0, print(n, " checked through b=", b)))};
print(n, " none through ", BMAX);
