\\ A072532: a(0)=1, a(n) = least prime k*a(n-1)-1 with k>1 (BPSW pseudoprime test).
\\ Print n, k, a(n-1) digits, k < a(n-1), and max of k/log(a(n-1))^2.
a = 1; mx = 0.;
for (n = 1, 160, k = 2; while (!ispseudoprime(k*a - 1), k++); r = if (a > 2, k / log(a)^2, 0.); mx = max(mx, r); print(n, " ", k, " ", #digits(a), " ", k < a, " ", r); a = k*a - 1);
print("max k/log^2 a: ", mx);
