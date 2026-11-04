# A226160 / A226188: least k with H_k > c n, c = 1/phi resp. 2/3.
# a(n) = exp(c n - gamma + o(1)), so a(n+1)/a(n) -> exp(c).  Exact search
# with H_k = log k + gamma + 1/(2k) - 1/(12k^2) + ... (mpmath harmonic).
#
import mpmath as mp
mp.mp.dps = 40
for name, c in (("A226160", 1 / mp.phi), ("A226188", mp.mpf(2) / 3)):
  out = []
  for n in range(1, 41):
    t = c * n
    k = int(mp.floor(mp.exp(t - mp.euler)))
    k = max(k - 3, 1)
    while mp.harmonic(k) <= t: k += 1
    while k > 1 and mp.harmonic(k - 1) > t: k -= 1
    out.append(k)
  print(name, out[:12], "ratio a(40)/a(39) =", mp.nstr(mp.mpf(out[-1]) / out[-2], 10), " exp(c) =", mp.nstr(mp.exp(c), 10))
