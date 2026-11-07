n2=1186095; print(factor(n2));
forprime(p=3,10^6, if(Mod(2,p)^n2==1 && Mod(3,p)^n2==1, print("P1 p=",p); break));
print(Mod(2,1210483)^n2, " ", Mod(3,1210483)^n2);
n1=3438721; print([Mod(2,23)^n1, Mod(3,23)^n1, Mod(2,331)^n1, Mod(3,331)^n1, Mod(2,487891)^n1, Mod(3,487891)^n1]);
print("gcd3 n2 = ", gcd(2^n2-3,3^n2-3), "  gcd1>1: ", gcd(2^n2-1,3^n2-1)>1, " gcd2>1: ", gcd(2^n2-2,3^n2-2)>1);
quit
