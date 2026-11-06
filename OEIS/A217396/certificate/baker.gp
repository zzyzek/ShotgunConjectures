\\ y^3 - y + 8 = 2^m.  K = Q(al), al^3 - al + 8 = 0, h = 1, eps = -6 al - 13.
\\ y - al = +-eps^a * pi1^b1 pi2^b2 pi3^b3, at most one b_i >= 2, others in {0,1}.
\\ Real embedding: Lam = 3 log|y - al1| - m log 2 = 3a*le + sum_i b_i*l_i,
\\ l_i = 3 log|pi_i(al1)| - log 2,  |Lam| < 8 * 2^(-m/3) for y >= 10.
default(realprecision, 400);
f = x^3 - x + 8;
K = bnfinit(f, 1);
r = polroots(f); al1 = real(r[1]);
P = idealprimedec(K, 2);
pis = vector(3, i, nfbasistoalg(K, bnfisprincipal(K, P[i])[2]));
eps = Mod(-6*x - 13, f);
ev(g) = subst(lift(g), x, al1);
\\ check generators: norms +-2, valuations
for(i=1,3, print("pi", i, " = ", lift(pis[i]), " N = ", norm(pis[i]), " vals ", [nfeltval(K, pis[i], P[j]) | j <- [1..3]]));
print("N(eps) = ", norm(eps));
le = log(abs(ev(eps)));
l = vector(3, i, 3*log(abs(ev(pis[i]))) - log(2));
\\ absolute logarithmic height of an element of K
ht(g) = {
  my(mp = minpoly(g), d, rr);
  mp = mp * denominator(content(mp)); mp = mp / content(mp);
  d = poldegree(mp); rr = polroots(mp);
  (log(abs(pollead(mp))) + sum(j = 1, d, log(max(1, abs(rr[j]))))) / d;
}
D = 3; n = 3;
CM = 1.4 * 30^(n+3) * n^4.5 * D^2 * (1 + log(D));
Amax(g, lg) = max(max(D * ht(g), abs(lg)), 0.16);
A1 = Amax(eps, le);
Mbig = 0;
{
for (i = 1, 3,
  my(g2 = pis[i]^3 / 2, A2 = Amax(g2, l[i]));
  forvec (s = vector(3, j, [0, 1]),
    if (s[i] != 0, next);
    my(g3 = prod(j = 1, 3, (pis[j]^3 / 2)^s[j]), c = sum(j = 1, 3, s[j] * l[j]), A3);
    A3 = if (g3 == 1, 1, Amax(g3, c));
    \\ |3a| <= (m*|l_i| + |c| + 1)/|le| =: K0 * m for m >= 1
    my(K0 = (abs(l[i]) + abs(c) + 1) / abs(le), m = 10.);
    \\ solve (m/3) log 2 - log 8 < CM*A1*A2*A3*(1 + log(K0 m)) by iteration
    for (it = 1, 200, m = 3 * (log(8) + CM*A1*A2*A3*(1 + log(max(K0, 1) * m))) / log(2));
    print("case i=", i, " s=", s, " A=", [A1, A2, A3], " K0=", K0, " m < ", m);
    Mbig = max(Mbig, m)));
}
print("Matveev bound m < ", Mbig);
\\ save for reduction
writebin("baker.bin", [le, l, Mbig]);
