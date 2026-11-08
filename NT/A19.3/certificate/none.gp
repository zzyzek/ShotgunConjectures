{foreach([42565109, 52274777, 111827383], n,
  print(n, " factor ", factor(n), " ispower ", ispower(n));
  \\ fraction of b < 2000 classes where n-2^b, n+2^b have a factor < 1000
  my(c1=0,c2=0); for(b=1,2000, if(#factor(abs(n-2^b),1000)[,1] > 1 || abs(n-2^b)%2==0, c1++); if(#factor(n+2^b,1000)[,1]>1, c2++)); print(" smallfactor fractions ", c1/2000., " ", c2/2000.);
  \\ prime powers with a >= 2 for b <= 5000
  my(f=0); for(b=1,5000, foreach([abs(n-2^b), n+2^b], v, my(k=ispower(v,,&r)); if(k && ispseudoprime(r), print("  prime power ", b, " ", r, "^", k); f=1))); )}
