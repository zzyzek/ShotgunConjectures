\\ A164848 from the definitions: A026741(n)/A051712(n+1), A051712(n) = numerator(b(n)-b(n+1)),
\\ b(n) = n/((n+1)(n+2)). Checks the listed data, period 24 and Howroyd's formula for n <= 10^5.
b(n) = n/((n+1)*(n+2));
A051712(n) = numerator(b(n) - b(n+1));
A026741(n) = if(n%2, n, n/2);
a(n) = A026741(n)/A051712(n+1);
data = [1,1,3,2,1,3,1,4,3,1,1,6,1,1,3,4,1,3,1,2,3,1,1,12,1,1,3,2,1,3,1,4,3,1,1,6,1,1,3,4,1,3,1,2,3,1,1,12,1,1,3,2,1,3,1,4,3,1,1,6,1,1,3,4,1,3,1,2,3,1,1,12,1,1,3,2,1,3,1,4,3,1,1,6,1,1,3,4,1,3,1,2,3,1,1,12,1,1,3,2,1,3,1,4,3];
for(n = 1, #data, if(a(n) != data[n], error("data mismatch at ", n)));
N = 10^5;
for(n = 1, N, v = a(n); if(type(v) != "t_INT", error("not integer at ", n)); \
  if(v != a((n-1)%24 + 1), error("period fails at ", n)); \
  if(v != gcd(12, n/gcd(2, n)), error("Howroyd fails at ", n)));
print("ok ", #data, " terms, n <= ", N);
