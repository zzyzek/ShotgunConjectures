\\ Morrison N+1 test (Morrison 1975): N+1 = 2^a 5^b fully factored. N is prime if for every
\\ prime r | N+1 there are P, Q with D = P^2-4Q, kronecker(D,N) = -1, gcd(N,2QD) = 1,
\\ U_{N+1} = 0 mod N and gcd(U_{(N+1)/r}, N) = 1 (Lucas sequence U(P,Q)).
U(P,Q,m,N)=lift((Mod([P,-Q;1,0],N)^m)[2,1]);
okr(N,r)={for(P=1,60, for(Q=-30,30, my(D=P^2-4*Q); if(Q!=0 && kronecker(D,N)==-1 && gcd(N,2*Q*D)==1,
  if(U(P,Q,N+1,N)!=0, return(0)); if(gcd(U(P,Q,(N+1)/r,N),N)==1, return(1)))));0}
morrison(a,b)={my(N=2^a*5^b-1);
  if(N<10^6, return(isprime(N)));
  if(a>0 && !okr(N,2), return(0)); if(b>0 && !okr(N,5), return(0)); 1}
{
v=readvec("tocert.txt"); bad=0;
for(i=1,#v, my(a=v[i][1],b=v[i][2]); if(!morrison(a,b), bad++; print("FAIL ",a," ",b)));
print("certified ",#v," failures ",bad);
}
