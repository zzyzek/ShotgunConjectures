default(parisizemax, 1500000000);
\\ For each n <= NMAX, all integers k >= 0 with
\\   B_k(n) = sum_j binomial(k,j) tau(n-j) = 0     (A097806^k * tau)
\\   S_k(n) = sum_j binomial(k-1+j,j) tau(n-j) = 0 (k-fold partial sums)
\\ B_k(n), S_k(n) are polynomials in k of degree n-1; we list their nonnegative
\\ integer roots via factor over Q.
NMAX = 400;
t = vector(NMAX, n, ramanujantau(n));
introots(P) = {if(type(P)!="t_POL", return([])); my(R = nfroots(,P), r = List()); for(i=1,#R, if(denominator(R[i])==1 && R[i]>=0, listput(r,R[i]))); Vec(r)};
for(n=1, NMAX, B = sum(j=0, n-1, binomial(x,j)*t[n-j]); S = sum(j=0, n-1, binomial(x-1+j,j)*t[n-j]); rb = introots(B); rs = introots(S); if(#rb || #rs, print("n=",n," B roots k=",rb," S roots k=",rs)));
print("done NMAX=", NMAX);
