# A113599 (pigeonhole proof in the entry): ceil(floor(9*10^(n-1)/n) / C(n+9,9)) >= n
# for 4 <= n <= 2000, and the ratio of successive bounds exceeds 1 from n = 4 on.
from math import comb
f = lambda n: -(-(9 * 10**(n-1) // n) // comb(n + 9, 9))
print(all(f(n) >= n for n in range(4, 2001)))
