\\ Writes the prime factorizations of a(1..64) for A180710 (a(n) = sigma(2^(n-1) a(n-1))) and checks sigma(n) | a(n).
default(parisizemax, 1500000000);
mulf(A,B) = matreduce(matconcat([A;B]));
F = matrix(0,2); first = 0;
for(n=2, 64, G = mulf(F, Mat([2, n-1])); H = matrix(0,2); \
  for(i=1, #G~, if(G[i,2]>0, H = mulf(H, factor((G[i,1]^(G[i,2]+1)-1)/(G[i,1]-1))))); F = H; \
  if(vecmin(vector(#F~, i, isprime(F[i,1]))) != 1, error("non-prime factor")); \
  write("factorizations.txt", n, " ", vector(#F~, i, [F[i,1], F[i,2]])); \
  r = lift(prod(i=1,#F~, Mod(F[i,1], sigma(n))^F[i,2])); \
  if(r != 0 && !first, first = n; print("first failure n=", n, " sigma(n)=", sigma(n), " a(n) mod sigma(n)=", r)));
print("a(64) has ", #digits(factorback(F)), " digits");
