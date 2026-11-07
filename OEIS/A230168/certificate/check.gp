\\ Primes 45*2^n-1 for n <= 2000 all end in 9; n = 0 gives 44.
{c=0; for(n=0,2000, my(p=45*2^n-1); if(ispseudoprime(p), c++; if(p%10!=9, error("bad ",n)))); print("primes found: ",c," all == 9 mod 10");}
quit
