\\ A210456: a(n) = period of n-step Fibonacci numbers mod 9.
\\ (1) For n = 2..100: a(n) (b-file) = 3 * ord3(n), ord3 = order of x modulo
\\     h = 1 - x - ... - x^n over F_3; so 3 | a(n).
\\ (2) ord3(3^m - 1) = 3^(2m) - 1 and ord3(3^m) = 3^(2m) + 3^m + 1 for m = 1..6
\\     (with (1) this gives Helenius's closed forms; b-file covers m <= 4).
\\ (3) the trace argument: s_1 = 1, s_3 = 7 (n >= 3) or 4 (n = 2), so s_3 != s_1 mod 9.
ordx(n) = {
  my(h = Mod(1,3) - sum(i=1,n, Mod(1,3)*x^i), F = factor(h), L = 1);
  for(i=1, #F~, my(g = F[i,1], e = F[i,2], d = poldegree(g), q = 3^d - 1, o = q, fa = factor(q));
    for(j=1, #fa~, while(o % fa[j,1] == 0 && Mod(Mod(1,3)*x, g)^(o/fa[j,1]) == 1, o /= fa[j,1]));
    my(t = 1); while(t < e, t *= 3);
    L = lcm(L, o * t));
  L;
}
v = readvec("b210456.vec");
for(n=2, #v, if(v[n] != 3*ordx(n), error("ratio fails at n=", n)));
print("(1) a(n) = 3*ord3(n) for n = 2..", #v);
{for(m=1, 6, my(q = 3^m);
  if(ordx(q-1) != q^2-1, error("case A fails m=", m));
  if(ordx(q) != q^2+q+1, error("case B fails m=", m)));}
print("(2) ord3(3^m-1) = 3^(2m)-1, ord3(3^m) = 3^(2m)+3^m+1 for m = 1..6");
for(n=2, 40, my(f = x^n - sum(i=0,n-1,x^i), s = polsym(f, 3)); if(s[2] != 1 || s[4] != if(n==2,4,7), error("traces n=",n)));
print("(3) s_1 = 1, s_3 = 7 (n>=3), 4 (n=2) for n = 2..40");
