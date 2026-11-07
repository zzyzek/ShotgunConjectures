\\ A096123: recompute a(n) (name reading: least k with (n-k)! | n!/(n-k)!) for n <= 24,
\\ compare with the OEIS data, and confirm a(2p) < (2p)!/(p-1)! for primes p <= 200.
a(n) = for(k = 0, n, if((n!/(n-k)!) % (n-k)! == 0, return(n!/(n-k)!)));
data = [1,2,6,12,60,120,840,1680,15120,5040,55440,665280,8648640,17297280,259459200,518918400,8821612800,17643225600,335221286400,670442572800,14079294028800,28158588057600,647647525324800,1295295050649600];
ok = 1; for(n = 1, 24, if(a(n) != data[n], ok = 0; print("mismatch ", n)));
print("data match n<=24: ", ok);
bad = 0; forprime(p = 2, 200, if(!(a(2*p) < (2*p)!/(p-1)!), bad++));
print("primes p<=200 with a(2p) >= (2p)!/(p-1)!: ", bad);
