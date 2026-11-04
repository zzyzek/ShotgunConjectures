\\ Certify the A051451 witness: n = 35, A000961(35) = 89, a(35) = lcm(1..89).
L=lcm(vector(89,i,i)); v=[x | x<-[1..89], x==1 || isprimepower(x)];
print("A000961(35) = ",v[35],"; a(35) digits = ",#digits(L));
print("L+17159, L+17161 proven prime: ",isprime(L+17159)," ",isprime(L+17161),"; 17161 = ",factor(17161));
c=0; forstep(m=1,17157,2, if(ispseudoprime(L+m)&&ispseudoprime(L+m+2), c++)); print("twin pairs with offset < 17159 (BPSW, never rejects primes): ",c);
