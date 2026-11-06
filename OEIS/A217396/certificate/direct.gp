c = 0;
for (m = 0, 5000, my(y0 = sqrtnint(2^m, 3)); for (y = max(-2, y0 - 3), y0 + 3, if (y^3 - y + 8 == 2^m, c++; print([y, m]))));
print("count ", c);
\\ Ramanujan-Nagell cross-check: x^2 + 7 = 2^N, N <= 5000
for (N = 0, 5000, my(v = 2^N - 7); if (v >= 0 && issquare(v), print("RN ", [sqrtint(v), N])));
