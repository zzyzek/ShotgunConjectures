a(n)=my(m=1,A=2^n,B=3^n);while(gcd(A-m,B-m)>1,m++);m;
N=40000;for(n=1,N,my(v=a(n));if(v>=3||n%330==121,print(n," ",v," ",n%330)));
quit
