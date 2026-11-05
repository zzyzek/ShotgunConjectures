# A182336: a(n) = least m >= n with popcount(n xor m) = 4. Checks n+1 <= a(n) <= 9n/8+1
# for 96 < n < LIMIT, lists the failures n <= 96, and checks the explicit witness used in
# the Lean proof (block table for n mod 64 < 56, m = n + 2^j otherwise) for 112 <= n < LIMIT.
import sys
LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
pc = lambda x: bin(x).count("1")
def a(n):
    m = n
    while pc(n ^ m) != 4: m += 1
    return m
print("failures n <= 96:", [n for n in range(97) if 8 * a(n) > 9 * n + 8])
print("failures 96 < n < LIMIT:", [n for n in range(97, LIMIT) if not (n + 1 <= a(n) and 8 * a(n) <= 9 * n + 8)])
bad = []
for n in range(112, LIMIT):
    r = n % 64
    if r < 56:
        rr = min(x for x in range(r + 1, 64) if pc(r ^ x) == 4)
        m = n - r + rr
        assert rr - r <= 15
    else:
        u = n // 8; j = ((u + 1) & -(u + 1)).bit_length() - 1
        assert j >= 3
        m = n + 2 ** j
    if not (pc(n ^ m) == 4 and n < m and 8 * m <= 9 * n + 8): bad.append(n)
print("witness failures:", bad)
