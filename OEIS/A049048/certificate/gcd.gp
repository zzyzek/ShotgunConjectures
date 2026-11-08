\\ For 2 <= n < m <= M print every gcd(n!-1, m!-1) > 1 and whether it is a pseudoprime.
M = 1200;
f = vector(M, k, k! - 1);
cnt = 0;
for (m = 3, M, for (n = 2, m - 1, g = gcd(f[n], f[m]); if (g > 1, cnt++; print(n, " ", m, " ", g, " ", ispseudoprime(g)))));
print("pairs with gcd>1: ", cnt);
