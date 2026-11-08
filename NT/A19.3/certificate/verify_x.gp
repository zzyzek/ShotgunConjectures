\\ Independent PARI re-check of verify_x.py: x odd, L, S (vector of primes).
\\ (1) every b mod L: gcd(x - 2^b, S) and gcd(x + 2^b, S) nontrivial;
\\ (2) single-prime classes: exponents a with e*p^a = x -+ 2^b excluded using
\\     constraints mod 2^K (b >= K) and mod auxiliary primes q with ord_q(2) | L;
\\ (3) b < B0 + L directly: |x -+ 2^b| has a prime factor in S and is not a power of it.
vx(x, L, S, K, qmax) = {
  my(P = prod(i=1,#S,S[i]), single = List(), aux = List(), bad = 0, B0);
  for(i=1,#S, if(L % znorder(Mod(2,S[i])), error("order")));
  for(b=0, L-1, foreach([-1,1], s,
    my(h = select(p -> (x + s*2^b) % p == 0, S));
    if(#h == 0, error("uncovered ", b, " ", s));
    if(#h == 1, listput(single, [s, b, h[1]]))));
  forprime(q=3, qmax, if(L % znorder(Mod(2,q)) == 0, listput(aux, q)));
  foreach(single, c, my(s = c[1], b0 = c[2], p = c[3]);
    foreach(if(s == -1, [1,-1], [1]), e,
      my(M = 2^K, o2 = znorder(Mod(p, M)), A = [], m = o2);
      A = select(a -> (e*Mod(p,M)^a - x) == 0, [0..o2-1]);
      foreach(aux, q, if(#A == 0, break); if(q == p, next);
        my(oq = znorder(Mod(p,q)), y = Mod(e*(x + s*2^b0), q), Aq, mm, An);
        Aq = select(a -> Mod(p,q)^a == y, [0..oq-1]);
        mm = lcm(m, oq); if(mm > 10^6, next);
        An = select(a -> setsearch(Set(A), a % m) && setsearch(Set(Aq), a % oq), [0..mm-1]);
        A = An; m = mm);
      if(#A, bad++; print("not excluded ", [s,b0,p,e,m,#A]))));
  B0 = max(K, #binary(x) + 1);
  for(b=0, B0 + L, foreach([-1,1], s, my(v = abs(x + s*2^b), h = select(p -> v % p == 0, S));
    if(v <= 1 || #h == 0, error("small b ", b));
    foreach(h, p, my(w = v); while(w % p == 0, w /= p); if(w == 1, error("prime power ", b, " ", s)))));
  print("single classes ", #single, " not excluded ", bad);
  bad == 0
};
