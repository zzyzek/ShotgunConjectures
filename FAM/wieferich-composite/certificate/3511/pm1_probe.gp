\\ For each prime p of data/factor3510.out (largest first), try to factor p - 1
\\ with a 60 s alarm; print the size of any composite part left.
default(parisize, 200000000); default(nbthreads, 1);
V = readvec("data/factor3510.vec");
{
for(i = 1, #V, my(p = V[i], f, t);
  if(p < 10^25, next);
  t = getwalltime();
  f = alarm(60, factor(p - 1)); if(type(f) == "t_ERROR", f = 0);
  if(f === 0, print(#Str(p), " digits: TIMEOUT"),
    print(#Str(p), " digits: ok ", getwalltime() - t, " ms, largest q ", #Str(vecmax(f[,1])), " digits")));
}
