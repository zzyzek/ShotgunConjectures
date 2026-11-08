\\ For each odd n read from file HARD (one per line), find b >= 1 with n + 2^b or
\\ |n - 2^b| prime, proved by isprime (APRCL/ECPP), searching b up to BMAX.
\\ Output lines: n b sign(+1: n+2^b, -1: 2^b-n or n-2^b) digits.
hardfile = getenv("HARDFILE"); BMAX = eval(getenv("BMAX"));
v = readvec(hardfile);
{for(i=1, #v, n = v[i]; got = 0;
  for(b=1, BMAX,
    t = 2^b;
    c = abs(n - t);
    if(c > 1 && ispseudoprime(c) && isprime(c), print(n, " ", b, " -1 ", #Str(c)); got = 1; break);
    c = n + t;
    if(ispseudoprime(c) && isprime(c), print(n, " ", b, " 1 ", #Str(c)); got = 1; break));
  if(!got, print(n, " NONE ", BMAX)))};
