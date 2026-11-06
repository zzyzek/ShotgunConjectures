default(realprecision, 100);
f = x^3 - x + 8; K = bnfinit(f, 1);
P = idealprimedec(K, 2);
pis = vector(3, i, nfbasistoalg(K, bnfisprincipal(K, P[i])[2]));
u = pis[1]*pis[2]*pis[3]/2; print("pi1 pi2 pi3 / 2 = ", lift(u), " unit: ", bnfisunit(K, lift(u)));
