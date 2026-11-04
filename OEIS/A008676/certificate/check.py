# A008676: coefficients of 1/((1-x^3)(1-x^5)) vs floor(2(n+3)/3) - floor(3(n+3)/5).
# Both sides are degree-1 quasi-polynomials of period 15, so 30 terms suffice;
# this checks n < 3000.
#
N = 3000
a = [0] * N
for i in range(0, N, 3):
  for j in range(i, N, 5): a[j] += 1
print("agree n < 3000:", all(a[n] == 2*(n + 3)//3 - 3*(n + 3)//5 for n in range(N)))
