# A143132: binomial transform of (1,5,15,35,70,0,...); compare with the entry
# data and test the last-digit pattern 1,6,6,6 for n < 10^4.
from math import comb
c = [1, 5, 15, 35, 70]
a = lambda n: sum(comb(n, k) * c[k] for k in range(min(n, 4) + 1))
data = [1,6,26,96,321,876,2006,4026,7321,12346,19626,29756,43401,61296,84246,113126,148881,192526,245146,307896,382001,468756,569526,685746,818921,970626,1142506,1336276,1553721,1796696,2067126,2367006,2698401,3063446]
assert [a(n) for n in range(len(data))] == data
assert all(a(n) % 10 == (1 if n % 4 == 0 else 6) for n in range(10000))
print("OK", len(data), "terms; digit pattern for n < 10000")
