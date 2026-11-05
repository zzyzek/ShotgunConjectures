\\ For each d | 3510: bit size of Phi_d(2) and of the cofactor left after dividing out
\\ every prime p = 1 (mod d) below 2^26 and the prime factors of d (Phi_d(2) has no other
\\ prime factors), with a probable-prime test of the cofactor. Lists the pieces of
\\ 2^3510 - 1 whose factorization this quick pass does not finish.
{
fordiv(3510, d,
  my(c = polcyclo(d, 2), r);
  r = c;
  my(fd = factor(d)[,1]);
  for(i = 1, #fd, while(r % fd[i] == 0, r /= fd[i]));
  forstep(p = d + 1, 2^26, d, if(isprime(p), while(r % p == 0, r /= p)));
  print(d, " bits=", #binary(c), " cofactor_bits=", if(r == 1 || ispseudoprime(r), 0, #binary(r))));
}
