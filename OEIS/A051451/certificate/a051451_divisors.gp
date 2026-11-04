\\ A051451, n = 35: for every odd offset m < 17159 with no prime <= 89 dividing
\\ m or m+2, print (m, s, d) with d a nontrivial divisor of L + m + s.
L=lcm(vector(89,i,i));
sf(x)=forprime(q=97,200000, if(x%q==0, return(q))); 0;
{forstep(m=1,17157,2, if(gcd(m,L)==1 && gcd(m+2,L)==1,
  s=0; d=sf(L+m); if(!d, s=2; d=sf(L+m+2));
  if(!d, s=if(!ispseudoprime(L+m),0,2); d=factor(L+m+s)[1,1]);
  print("(",m,", ",s,", ",d,"),")))}
print("L = ",L);
print("isprime(L+17159), isprime(L+17161): ",isprime(L+17159)," ",isprime(L+17161));
quit
