\\ Try PARI's factor (rho, ECM, ...) on the composite cofactor of p - 1 for the
\\ largest prime p (index IDX in data/factor3510.vec), with an alarm of SECS seconds.
default(parisize, 200000000); default(nbthreads, 1);
V = readvec("data/factor3510.vec");
p = V[IDX]; f = factor(p - 1, 2^24); C = f[#f~, 1];
r = alarm(SECS, factor(C));
print(if(type(r) == "t_ERROR", "timeout", r));
