Read("maxdeg.g");
for n in [32, 64] do
  t := Runtime();
  r := MaxDeg2(n);
  Print(n, " ", r[1], " ", r[2], " ", r[3], " time_ms=", Runtime()-t, "\n");
od;
QUIT;
