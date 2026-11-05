\\ Combine the factordb factor lists (data/factors3510_claimed.txt, "d p e") with
\\ PARI factorizations of the small pieces Phi_d(2) and verify:
\\ every claimed piece multiplies to Phi_d(2), every factor passes isprime
\\ (proven primality in PARI), and the total product is 2^3510 - 1.
\\ Prints "p e" lines (merged over d) to stdout.
default(parisize, 200000000); default(nbthreads, 1);
big = [351, 585, 702, 1170, 1755, 3510];
L = readvec("data/factors3510_claimed.vec");
F = Map();
add(p, e) = if(mapisdefined(F, p), mapput(F, p, mapget(F, p) + e), mapput(F, p, e));
{
fordiv(3510, d,
  my(c = polcyclo(d, 2));
  if(setsearch(Set(big), d),
    my(pr = 1);
    for(i = 1, #L, if(L[i][1] == d,
      if(!isprime(L[i][2]), error("not prime ", L[i][2]));
      pr *= L[i][2]^L[i][3]; add(L[i][2], L[i][3])));
    if(pr != c, error("product mismatch at d=", d)),
    my(f = factor(c));
    for(j = 1, #f~, add(f[j,1], f[j,2]))));
}
M = Mat(F);
if(prod(i = 1, #M~, M[i,1]^M[i,2]) != 2^3510 - 1, error("total product mismatch"));
for(i = 1, #M~, print(M[i,1], " ", M[i,2]));
