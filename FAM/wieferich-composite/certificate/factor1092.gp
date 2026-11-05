\\ Factor 2^1092 - 1 through cyclotomic and Aurifeuillian pieces, all <= 144 bits.
default(parisize, 200000000);
N = 2^1092 - 1;
x = 2^136;
A = 2*x^2 - 2*x + 1; B = 2*x^2 + 2*x + 1;
\\ A*B = 2^546 + 1
pieces = [];
fordiv(546, d, pieces = concat(pieces, [polcyclo(d, 2)]));
fordiv(1092, d, if(546 % d, my(c = polcyclo(d, 2)); pieces = concat(pieces, [gcd(c, A), c / gcd(c, A)])));
F = Map();
{
for(i = 1, #pieces,
  my(f = factor(pieces[i]));
  for(j = 1, #f~,
    my(p = f[j,1], e = f[j,2]);
    if(mapisdefined(F, p), mapput(F, p, mapget(F, p) + e), mapput(F, p, e))));
}
M = Mat(F);
if(prod(i = 1, #M~, M[i,1]^M[i,2]) != N, error("product mismatch"));
for(i = 1, #M~, if(!isprime(M[i,1]), error("not prime")));
for(i = 1, #M~, print(M[i,1], " ", M[i,2]));
