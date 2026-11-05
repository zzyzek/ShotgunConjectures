default(parisize, 200000000); default(nbthreads, 1);
V = readvec("data/factor3510.vec");
p = V[1]; f = factor(p - 1, 2^24); C = f[#f~, 1];
B1 = 10^5; K = 1; forprime(q = 2, B1, K *= q^logint(B1, q));
t = getwalltime();
a = random(C); x = random(C); y = random(C); b = Mod(y^2 - x^3 - a*x, C);
E = ellinit([a, lift(b)], Mod(1, C));
r = iferr(ellmul(E, [Mod(x, C), Mod(y, C)], K), err, err);
print(getwalltime() - t, " ms; ", type(r));
