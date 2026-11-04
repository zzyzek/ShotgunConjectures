\\ A088276: find small r (odd, 5 does not divide r, r != 2 mod 3) such that 10^k + r is
\\ divisible by one of 7, 11, 13, 37 for every k (period lcm(ord)=6), so never prime.
P=[7,11,13,37];
cov(r)=for(k=0,5, my(ok=0); for(i=1,#P, if((Mod(10,P[i])^k+r)==0, ok=1;break)); if(!ok,return(0))); 1;
{
L=List();
forstep(r=1,2*10^6,2, if(r%5==0||r%3==2,next); if(cov(r), listput(L,r); if(#L>=5,break)));
print("A088276 covering r (7,11,13,37): ",L);
r=L[1]; print("r=",r," index n=", sum(j=1,r,(j%2==1)&&(j%5!=0)), " r mod 3=",r%3);
\\ sanity: explicit k up to 2000 all composite with a covering prime factor
bad=0; for(k=1,2000, my(N=10^k+r); if(gcd(N,7*11*13*37)==1 || N==7||N==11||N==13||N==37, bad++)); print("k<=2000 failures of covering: ",bad);
}
{
\\ A101462: 2^k - 509203 never prime: covering {3,5,7,13,17,241}, period 24
p=509203; Q=[3,5,7,13,17,241]; print("509203 prime? ",isprime(p), "  pi(p)=",primepi(p));
ok=1; for(k=0,23, my(c=0); for(i=1,#Q, if(Mod(2,Q[i])^k==p, c=1)); if(!c, ok=0; print("uncovered k mod 24: ",k))); print("covered all residues mod 24: ",ok);
\\ 2^k - p positive requires k>=19; check no value equals a covering prime
for(k=19,40, if(setsearch(Set(Q),2^k-p), print("equals covering prime at k=",k)));
}
