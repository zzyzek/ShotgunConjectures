\\ For each prime p = prime(n), n in [n1, n2], find a palindromic prime with digit sum p
\\ whose digits lie in DIG (A083183: [2,3,5,7]; A083184: [0..9]); first digit from FIRST;
\\ odd length 2k+1 with middle digit c from ODD.
\\ Random half-strings with half-sum S = (p - c)/2; k swept upward from the least feasible value,
\\ preferring k near S / mean(DIG). Prints n, p, number of digits, witness.
\\ Primality: ispseudoprime (BPSW); if PROVE, also isprime (APR-CL proof). Not necessarily the smallest witness.
witness(p, DIG, FIRST, ODD, PROVE) =
{
  my(mind = vecmin(DIG), maxd = vecmax(DIG), mean = vecsum(DIG) / #DIG, S, h, v, P, k0);
  for (rr = 0, 60,
    foreach(ODD, c,
      if ((p - c) % 2 || p - c < 0, next);
      S = (p - c) / 2;
      k0 = max(1, round(S / mean));
      foreach([k0 + rr, k0 - rr], k,
        if (k < 1, next);
        if (S < vecmin(FIRST) + (k - 1) * mind || S > vecmax(FIRST) + (k - 1) * maxd, next);
        for (tries = 1, 300,
          h = vector(k, i, if (i == 1, FIRST[random(#FIRST) + 1], DIG[random(#DIG) + 1]));
          if (vecsum(h) != S, next);
          v = concat(concat(h, [c]), Vecrev(h));
          P = fromdigits(v);
          if (ispseudoprime(P) && (!PROVE || isprime(P)), return([2 * k + 1, P]))))));
  return(0);
}
\\ Up to 10 independent attempts per n (the random search can miss).
runlist(L, DIG, FIRST, ODD, PROVE) =
{
  foreach(L, n,
    my(p = prime(n), w = 0);
    for (att = 1, 10, w = witness(p, DIG, FIRST, ODD, PROVE); if (w != 0, break));
    if (w == 0, print("FAIL ", n, " ", p); next);
    print(n, " ", p, " ", w[1], " ", if (PROVE, "proved", "bpsw"), " ", w[2]));
}
run(n1, n2, DIG, FIRST, ODD, PROVE) =
{
  for (n = n1, n2,
    my(p = prime(n), w);
    w = 0;
    for (att = 1, 10, w = witness(p, DIG, FIRST, ODD, PROVE); if (w != 0, break));
    if (w == 0, print("FAIL ", n, " ", p); next);
    print(n, " ", p, " ", w[1], " ", if (PROVE, "proved", "bpsw"), " ", w[2]));
}
