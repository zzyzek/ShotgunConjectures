Read("maxdeg.g");
for n in [2..24] do
  r := MaxDeg2(n);
  Print(n, " ", r[1], " ", r[2], " ", r[3], "\n");
od;
QUIT;
