# A113249-A113256: for m = 0..12 and n < 300, a(m, 2n+1) = y(m, n)^2 with
# y(n) = 4 y(n-1) - m^2 y(n-2), y(0) = 2, y(1) = 8 - m^2 (exact integers).
ok = True
for m in range(13):
  a = [-1, 4, -13 + 6*(m-1) + 3*(m-1)**2, (m*m - 8)**2]
  for n in range(4, 601): a.append(m**4 * a[n-4] + (2*m)**2 * a[n-3] - 4 * a[n-1])
  y = [2, 8 - m*m]
  for n in range(2, 300): y.append(4 * y[-1] - m*m * y[-2])
  ok &= all(a[2*n + 1] == y[n]**2 for n in range(300))
print(ok)
