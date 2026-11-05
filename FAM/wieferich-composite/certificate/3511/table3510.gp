\\ Per d | 3510: digits of Phi_d(2) and of its prime factors (the factorization is the
\\ verified one in data/factor3510.out; each prime is assigned to the d it divides).
default(nbthreads, 1);
V = readvec("data/factor3510.vec");
{
fordiv(3510, d, my(c = polcyclo(d, 2), s = "");
  for(i = 1, #V, my(e = valuation(c, V[i])); if(e, s = Str(s, " ", #Str(V[i]), if(e > 1, Str("^", e), ""))));
  print(d, " | ", #Str(c), " |", s));
}
