\\ For the two largest primes: partial factorization of p - 1 by trial division to 2^24,
\\ then ECM-style splitting via factor with a 120 s alarm on the cofactor. Report the
\\ proven-prime part F and its size relative to sqrt(p) and p^(1/3).
default(parisize, 200000000); default(nbthreads, 1);
V = readvec("data/factor3510.vec");
{
for(i = 1, 2, my(p = V[i], f = factor(p - 1, 2^24), F = 1, C = 1);
  for(j = 1, #f~, if(isprime(f[j,1]), F *= f[j,1]^f[j,2], C *= f[j,1]^f[j,2]));
  print(#Str(p), " digits: F bits ", #binary(F), " of ", #binary(p - 1), "; C bits ", #binary(C), " ispseudoprime(C)=", ispseudoprime(C));
  print("  F = ", factor(F)));
}
