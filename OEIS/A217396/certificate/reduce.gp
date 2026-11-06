\\ Dujella-Petho / Legendre reduction of the Matveev bound (see baker.gp).
default(realprecision, 400);
f = x^3 - x + 8;
K = bnfinit(f, 1);
r = polroots(f); al1 = real(r[1]);
P = idealprimedec(K, 2);
pis = vector(3, i, nfbasistoalg(K, bnfisprincipal(K, P[i])[2]));
eps = Mod(-6*x - 13, f);
ev(g) = subst(lift(g), x, al1);
le = log(abs(ev(eps)));
l = vector(3, i, 3*log(abs(ev(pis[i]))) - log(2));
dist(t) = abs(t - round(t));
\\ one reduction step: given bound Mm on m, return new bound on m for case (i, s)
red(i, s, Mm) = {
  my(c = sum(j = 1, 3, s[j] * l[j]), kap = le / l[i], mu = c / l[i], cc = 8 / abs(l[i]));
  my(K0 = (abs(l[i]) + abs(c) + 1) / abs(le), M = ceil(K0 * Mm), best = 0, cf, q, pq, amax);
  \\ pi1 pi2 pi3 = 2 eps, so l1 + l2 + l3 = 3 le: if both other s_j = 1 the form is
  \\ (A + 3) le + (b - 1) l_i, homogeneous.
  if (vecsum(s) == 2, c = 0; M = M + 3);
  if (c == 0,
    \\ homogeneous: Legendre with max partial quotient
    cf = contfrac(kap); amax = 0; q = 1;
    for (k = 1, #cf, pq = contfracpnqn(cf[1..k]); q = pq[2, 1];
      if (k > 1, amax = max(amax, cf[k]));
      if (q > M, break));
    if (q <= M, error("cf too short"));
    \\ 2^(m/3) < cc (amax + 2) M  (also need cc 2^(-m/3) < 1/(2u), implied for larger m)
    best = max(3 * log(cc * (amax + 2) * M) / log(2), 3 * log(2 * cc * M) / log(2));
    return(best));
  \\ inhomogeneous: both signs of A, and A = 0
  best = 3 * log(cc / dist(mu)) / log(2);
  foreach ([kap, -kap], kk,
    cf = contfrac(kk); my(found = 0);
    for (k = 1, #cf, pq = contfracpnqn(cf[1..k]); q = pq[2, 1];
      if (q > 6 * M,
        my(e = dist(mu * q) - M * dist(kk * q));
        if (e > 0, best = max(best, 3 * log(cc * q / e) / log(2)); found = 1; break)));
    if (!found, error("no good convergent")));
  best;
}
Mm = 338056857948864962.;
{
for (round = 1, 4,
  my(newM = 0);
  for (i = 1, 3, forvec (s = vector(3, j, [0, 1]),
    if (s[i] != 0, next);
    newM = max(newM, red(i, s, Mm))));
  print("round ", round, ": m < ", newM);
  if (newM >= Mm - 1, break);
  Mm = ceil(newM));
}
print("final bound m <= ", Mm);
\\ direct check: all y >= -2 with y^3 - y + 8 = 2^m for m <= Mm (+ margin)
sols = List();
{
for (m = 0, Mm + 10,
  my(y0 = sqrtnint(2^m, 3));
  for (y = max(-2, y0 - 3), y0 + 3, if (y^3 - y + 8 == 2^m, listput(sols, [y, m]))));
for (y = -2, 10, my(v = y^3 - y + 8); if (v > 0 && v == 2^valuation(v, 2), listput(sols, [y, valuation(v, 2)])));
}
print("solutions (y, m): ", Set(Vec(sols)));
