\\ Independent check of n = 6 and n = 12: rigorous isprime, all d = 1 candidates below the witness.
f(n,a,d)=prod(i=0,n-1,a+i*d)+d;
{
foreach([[6,20161],[12,316234143227]], t, n=t[1]; W=t[2];
  print("n=",n," witness prime: ",isprime(W));
  for(d=1,10, a=1; while((v=f(n,a,d))<W, if(isprime(v), print("  smaller prime: a=",a," d=",d," v=",v)); a++));
  print("  done n=",n));
print("151201 = 5*..*10+1: ", f(6,5,1)==151201, "  20161 = 3*..*8+1: ", f(6,3,1)==20161);
}
