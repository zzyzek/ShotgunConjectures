\\ order of a square matrix over F_p via its minimal polynomial (same method as psi_order.gp)
matord(A, p) = {
  my(mp = minpoly(A), F = factormod(lift(mp), p), L = 1);
  for(k=1, #F~,
    my(f = F[k,1], e = F[k,2], o, d = poldegree(f), q = p^d - 1, t = 1);
    if(f == x, error("singular"));
    o = q; foreach(factor(q)[,1], r, while(o % r == 0 && Mod(Mod(x,p),f)^(o/r) == 1, o /= r));
    while(t < e, t *= p);
    L = lcm(L, o * t));
  L;
}
M(p) = matrix(p,p,i,j, if(i==1, if(j==1,Mod(1,p),Mod(0,p)), Mod(i-1,p)^(j-1)));
N(p) = matrix(p-1,p-1,a,j, Mod(a,p)^j);
FP(p) = {my(g=znprimroot(p), F=matrix(p-1,p-1,k,m, g^((k-1)*(m-1))), P=matrix(p-1,p-1,k,m, Mod(m-1 == (lift(g^(k-1)) % (p-1)),p))); F*P};
{
forprime(p=3, 31, my(oM=matord(M(p),p), oN=matord(N(p),p), oF=matord(FP(p),p), F=FP(p)/1, R=matrix(p-1,p-1,i,j,Mod(((i-1)+(j-1))%(p-1)==0,p)), G=matrix(p-1,p-1,k,m, znprimroot(p)^((k-1)*(m-1))));
  print(p, " ordPsi=", oM, " ordN=", oN, " ordFP=", oF, " ratio=", oM/oN, " F^2=-R:", G^2 == -R));
}
