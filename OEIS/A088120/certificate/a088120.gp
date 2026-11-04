\\ A088120: smallest prime prod_{i<n}(a+i*d) + d over a,d >= 1.
\\ Conjecture (2): the minimising d is 1 except n = 4, 5 (d = 2).
\\ Candidates are enumerated below a bound B that grows by 16x until a prime appears.
f(n,a,d)=prod(i=0,n-1,a+i*d)+d;
best(n)={my(B=4*f(n,1,1),L,a,d,v);
  while(1,
    L=List(); d=1;
    while(f(n,1,d)<B, a=1; while((v=f(n,a,d))<B, listput(L,[v,a,d]); a++); d++);
    L=vecsort(Vec(L),1);
    for(i=1,#L, if(ispseudoprime(L[i][1]), return(L[i])));
    B*=16)};
{
for(n=1,45, b=best(n);
  if(b[3]!=1 || n<=12, print("n=",n," a(n)=",b[1]," a=",b[2]," d=",b[3])));
print("done n<=45");
}
