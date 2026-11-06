\\ Check corrected newform-dimension formulas for OEIS A063289, A063305, A063321, A063337
\\ against PARI/GP mfdim (exact dim S_k^new(Gamma_1(N)), all characters: CHI = -1).
\\ OEIS indexing: offset 2, term a(n) is the weight n-1 dimension (a(2) = -1 is not a
\\ weight-1 dimension). Weights k = 2..80, i.e. n = 3..81.
\\ Run: gp -q newdim.gp
\\
default(parisize, 64000000);
K = 80;
\\ [A-number, level N, corrected formula in weight k, corrected formula in OEIS index n,
\\  printed (wiki) formula in index n, OEIS data a(2..)]
{
T = [ ["A063289", 16, k -> 9*k/2 - (-1)^k/4 - 27/4, n -> 9*n/2 + (-1)^n/4 - 45/4, n -> 9*n/4 + (-1)^n/4 - 45/4,
        [-1,2,7,11,16,20,25,29,34,38,43,47,52,56,61,65,70,74,79,83,88,92,97]],
      ["A063305", 32, k -> 18*k - 23, n -> 18*n - 41, n -> 18*n,
        [-1,13,31,49,67,85,103,121,139,157,175,193,211,229,247,265,283,301]],
      ["A063321", 48, k -> (54*k - 63 + (-1)^k)/2, n -> 13*(n + (n-1)%2) + 14*(n + n%2) - 72, n -> 13*(n + (n-1)%2) + 14*(n + n%2),
        [-1,23,49,77,103,131,157,185,211,239,265,293,319,347,373,401,427,455]],
      ["A063337", 64, k -> 72*k - 83, n -> 72*n - 155, n -> 72*n,
        [-1,61,133,205,277,349,421,493,565,637,709,781,853,925,997,1069,1141]] ];
}
{
for (i = 1, #T,
  my(id = T[i][1], N = T[i][2], fk = T[i][3], fn = T[i][4], fw = T[i][5], dat = T[i][6], ok = 1, badw = 0, badi = 0);
  for (k = 2, K,
    my(d = mfdim([N, k, -1], 0));
    if (fk(k) != d || fn(k + 1) != d, ok = 0; print(id, " MISMATCH at weight ", k, ": mfdim ", d, " formula ", fk(k)));
    if (fw(k + 1) == d, badi++);
    if (fw(k) == d, badw++));
  for (j = 2, #dat, if (dat[j] != mfdim([N, j, -1], 0), ok = 0; print(id, " data a(", j + 1, ") != mfdim weight ", j)));
  print(id, " N=", N, ": corrected formula = mfdim for k=2..", K, ": ", if (ok, "OK", "FAIL"),
        "; weight-1 mfdim = ", mfdim([N, 1, -1], 0), ", OEIS a(2) = ", dat[1],
        "; printed formula agrees at ", badi, " OEIS indices and ", badw, " weights in range"));
}
quit;
