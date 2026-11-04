# A101312: does "weekday u on the 13th" (equivalently any weekday on any day d) give a
# shifted copy of the Friday-the-13th sequence?  Full Gregorian 400-year cycle
# (1601-2000) and the Julian-like stretch 1901-2099 (period 28).
#
import datetime
def counts(wd, day, y0, n):
  return [sum(1 for m in range(1,13) if datetime.date(y,m,day).weekday()==wd) for y in range(y0, y0+n)]
F = counts(4, 13, 1601, 400)   # Friday=4
# day d, weekday w: same as 13th with weekday shifted, check all 7 weekdays on the 13th
res = {}
for u in range(7):
  G = counts(u, 13, 1601, 400)
  res[u] = [s for s in range(400) if all(G[i] == F[(i+s) % 400] for i in range(400))]
print({u: v[:5] for u, v in res.items()})
# Julian-like stretch 1901-2099
for u in range(7):
  G = counts(u, 13, 1901, 199); FF = counts(4, 13, 1901, 199)
  print(u, [s for s in range(28) if all(G[i] == FF[i+s] for i in range(199-28))][:3])
# Cross-check with Zeller's congruence (independent of datetime): weekday of the 13th.
def zeller(y, m, d):
  if m < 3: m += 12; y -= 1
  K, Jc = y % 100, y // 100
  h = (d + (13 * (m + 1)) // 5 + K + K // 4 + Jc // 4 + 5 * Jc) % 7
  return (h + 5) % 7   # 0 = Monday, ..., 4 = Friday
print("Zeller agrees with datetime on 1601-2000:", all(zeller(y, m, 13) == datetime.date(y, m, 13).weekday()
      for y in range(1601, 2001) for m in range(1, 13)))
