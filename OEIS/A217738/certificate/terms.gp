\\ Terms k <= N of A217738 (k(k+1) | F_k), only k = 0 mod 12 tested (proved necessary);
\\ classify k+1 as prime or composite and print composite cases with factorizations.
fibmod(n,m)=lift((Mod([1,1;1,0],m)^n)[1,2]);
N=10^6; c=0; cp=0; comp=List();
forstep(k=12,N,12, if(fibmod(k,k*(k+1))==0, c++; if(isprime(k+1), cp++, listput(comp,[k,factor(k),factor(k+1)]))));
print("terms<=",N,": ",c,"  with k+1 prime: ",cp);
for(i=1,min(#comp,40),print(comp[i]));
print("#composite k+1: ",#comp);
