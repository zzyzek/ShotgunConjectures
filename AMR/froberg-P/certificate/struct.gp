M(p) = matrix(p,p,i,j, if(i==1, if(j==1,Mod(1,p),Mod(0,p)), Mod(i-1,p)^(j-1)));
\\ N = psi restricted to {f(0)=0}, basis x^1..x^{p-1}
N(p) = matrix(p-1,p-1,a,j, Mod(a,p)^j);
\\ F = DFT of Z/(p-1) with generator g;  pi(k) = (g^k mod p) mod (p-1)
FP(p) = {my(g=znprimroot(p), F=matrix(p-1,p-1,k,m, g^((k-1)*(m-1))), P=matrix(p-1,p-1,k,m, Mod(m-1 == (lift(g^(k-1)) % (p-1)),p))); F*P};
{
forprime(p=3, 59, my(A=M(p), B=N(p), C=FP(p), cB=charpoly(B), cA=charpoly(A), mA=minpoly(A), cC=charpoly(C), e1=0, t=cB);
  while(subst(lift(t),x,1)%p==0, t=lift(t)/(x-1); t=Mod(1,p)*t; e1++);
  print(p, " cpA=(x-1)cpN:", cA==(x-1)*cB, " cpN=cpFP:", cB==cC, " cycA:", cA==mA, " mult1(N):", e1));
}
