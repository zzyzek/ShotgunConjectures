\\ ECM stage 1 (PARI ellmul over Z/CZ; a failed inversion reveals a factor) on the
\\ composite cofactor C of p - 1, p = V[IDX] (V = data/factor3510.vec), B1 = B1V,
\\ for NC curves. Prints every factor found. Usage: gp -q -D parisize=200000000, with
\\ IDX, B1V, NC (and optionally SEED) set before read("ecm_stage1.gp").
default(nbthreads, 1);
V = readvec("data/factor3510.vec");
p = V[IDX]; f = factor(p - 1, 2^24); C = f[#f~, 1];
K = 1; forprime(q = 2, B1V, K *= q^logint(B1V, q));
if(type(SEED) == "t_POL", SEED = 0);
setrand(IDX * 1000003 + B1V + 7919 * SEED);
{
for(i = 1, NC,
  my(a = random(C), x = random(C), y = random(C), b, E, r, g);
  b = lift(Mod(y^2 - x^3 - a*x, C));
  if(gcd(4*a^3 + 27*b^2, C) != 1, next);
  E = ellinit([a, b], Mod(1, C));
  r = iferr(ellmul(E, [Mod(x, C), Mod(y, C)], K), err, err);
  if(type(r) == "t_ERROR",
    g = gcd(lift(component(r, 2)), C);
    if(g > 1 && g < C, print("curve ", i, " factor ", g, " isprime ", isprime(g));
      C /= g; while(C % g == 0, C /= g))));
print("remaining C bits ", #binary(C), " isprime ", ispseudoprime(C));
}
