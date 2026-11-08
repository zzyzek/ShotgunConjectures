\\ term for even M: first prime x with x^x - M prime (PARI isprime of negatives = 0)
t(M)=forprime(x=2,100,my(y=x^x-M);if(isprime(y),return(y)));-1
\\ data check: M=2,4,...,38
v=vector(19,i,t(2*i)); print(v);
\\ two-digit primes appear
forprime(q=10,99, M=3125-q; if(t(M)!=q, print("FAIL ",q)));
print("q=97 M=",3125-97," t=",t(3028));
\\ count M with t(M)<100
c=0;forstep(M=2,4000,2,if(t(M)>0&&t(M)<100,c++));print(c)
