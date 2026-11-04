\\ A051451 (2013 wiki form): the first twin pair after a(n) = lcm(1..x), x = n-th prime power,
\\ is [a(n)+p, a(n)+p+2] with p, p+2 twin primes. Report n where the offset m of the first pair is not a lesser twin prime.
{
pp=[x | x<-[2..2000], isprimepower(x)]; L=1; t0=getabstime();
for(n=1,#pp, L=lcm(L,pp[n]); if(n<3, next);
  m=1; while(!(ispseudoprime(L+m) && ispseudoprime(L+m+2)), m+=2);
  if(!(isprime(m) && isprime(m+2)), print("n=",n," x=",pp[n]," first twin offset m=",m," factor m=",factor(m)," m+2=",factor(m+2)));
  if(getabstime()-t0>100000, print("stopped at n=",n," x=",pp[n]); break));
print("done");
}
