Read("maxdeg.g");
psi := n -> n * Product(Set(Factors(n)), p -> 1 + 1/p);
r := MaxDeg2(2*NN);
Print("even ", 2*NN, " a=", r[2], " 2psi=", 2*psi(NN), " ok=", r[2] = 2*psi(NN), "\n");
QUIT;
