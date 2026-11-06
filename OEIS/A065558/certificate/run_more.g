Read("maxdeg.g");
for n in [128, 25, 27, 49, 81] do
  t := Runtime();
  r := MaxDeg2(n);
  Print("pp ", n, " ", r[1], " ", r[2], " time_ms=", Runtime()-t, "\n");
od;
psi := n -> n * Product(Set(Factors(n)), p -> 1 + 1/p);
for n in [1..30] do
  t := Runtime();
  r := MaxDeg2(2*n);
  Print("even ", 2*n, " a=", r[2], " 2psi=", 2*psi(n), " ok=", r[2] = 2*psi(n), " time_ms=", Runtime()-t, "\n");
od;
QUIT;
