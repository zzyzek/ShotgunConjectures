\\ Primality of the two factors not certified in Lean: isprime(p, 2) (APRCL proof)
\\ and isprime(p, 1) (Pocklington-Lehmer, expected to fail since p - 1 is not factored).
default(nbthreads, 1);
V = readvec("data/factor3510.vec");
{
for(i = 1, 2, my(p = V[i], t = getwalltime());
  print(#Str(p), " digits: APRCL isprime(p,2) = ", isprime(p, 2), " (", getwalltime() - t, " ms)");
  print("  p mod 3510 = ", p % 3510, ", Phi_3510(2) % p = ", polcyclo(3510, 2) % p, ", Phi_1755(2) % p = ", polcyclo(1755, 2) % p));
}
