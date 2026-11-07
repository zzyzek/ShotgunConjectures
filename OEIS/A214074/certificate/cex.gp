g(n,m)=gcd(2^n-m,3^n-m);
a(n)=my(m=1);while(g(n,m)>1,m++);m;
c=chinese(Mod(121,330),Mod(23491,487890)); print("if-class: ",c);
n1=lift(c); print("n1=",n1," a(n1)=",a(n1)," factors gcd m=3 contains 487891: ",g(n1,3)%487891==0);
for(k=0,12, n=379107+k*403494; print("onlyif cand n=",n," n%330=",n%330," a=",a(n)));
quit
