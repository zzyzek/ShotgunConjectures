default(parisizemax, 1500000000);
default(realprecision, 600);
N=1205;
A=1.+O(x^N); B=exp(4*x+O(x^N))*1.;
for(it=1,60, A2=(A+B)/2; B=sqrt(A*B); A=A2; d=A-B; if(it%10==0, print("it ",it," ",vecmax(apply(abs,Vec(d))))));
s=A;
print(vector(21,n,round(polcoeff(s,n-1)*(n-1)!)));
forstep(n=100,1200,100, for(k=0,3, m=n+k; v=polcoeff(s,m); print(m," ",precision((abs(v))^(-1/m)*4/Pi,20), "  scaled=", precision(v*(Pi/4)^m*m*log(m)^2,10))));
