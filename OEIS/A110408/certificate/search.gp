\\ A110408: N_k(n) = (rev n repeated k times) followed by n, k >= 1.
\\ For n <= 2000, n = 1,3,7,9 mod 10, 3 !| n, n not a palindrome: smallest k <= KMAX
\\ with N_k a probable prime; print n with none found.
rev(n)=fromdigits(Vecrev(digits(n)));
KMAX=400;
{
cnt=0; miss=List();
forstep(n=1,2000,2, if(n%5==0 || n%3==0, next); r=rev(n); if(r==n, next);
  d=#digits(n); R=0; f=0;
  for(k=1,KMAX, R=R*10^d+r; if(ispseudoprime(R*10^d+n), f=k; break));
  cnt++; if(f==0, listput(miss,n)));
print("tested ",cnt," n; no PRP with k<=",KMAX,": ",miss);
}
