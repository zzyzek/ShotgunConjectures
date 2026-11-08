{
N=500;
for(a=0,N, for(b=0,N, if(a+b>0, my(p=2^a*5^b-1); if(p>1 && ispseudoprime(p), print(a," ",b)))));
}
