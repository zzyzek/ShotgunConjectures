\\ Order of psi: f -> sum_{a in F_p} f(a) x^a on polys of degree < p (Froberg et al. Problem P).
ordp(p) = {
  my(M = matrix(p,p,i,j, Mod(i-1,p)^(j-1)), mp, F, L = 1);
  for(i=1,p, M[1,i] = Mod(0,p)); M[1,1] = Mod(1,p);
  \\ row a=0: 0^0 = 1, 0^j = 0
  mp = minpoly(M);
  F = factormod(lift(mp), p);
  for(k=1, #F~,
    my(f = F[k,1], e = F[k,2], o, d = poldegree(f), q = p^d - 1, t = 1);
    if(f == x, error("singular"));
    o = q; foreach(factor(q)[,1], r, while(o % r == 0 && Mod(Mod(x,p),f)^(o/r) == 1, o /= r));
    while(t < e, t *= p);
    L = lcm(L, o * t));
  L;
}
forprime(p=3, 60, print(p, " ", ordp(p), " ", factor(ordp(p))));
