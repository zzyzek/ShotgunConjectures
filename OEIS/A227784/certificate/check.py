# Brute force: least k with -1 a sum of k d-th powers mod n (d = 2, 4), for n <= N;
# compare with the OEIS b-files (if given) and with the proved rules.
import sys
def least(n, d):
    if n == 1: return 0
    P = {pow(x, d, n) for x in range(n)}
    reach = {0}; k = 0
    while (n - 1) not in reach:
        reach = {(r + p) % n for r in reach for p in P}; k += 1
    return k
def bfile(path):
    try: return {int(a): int(b) for a, b in (l.split() for l in open(path) if l.strip() and not l.startswith('#'))}
    except OSError: return {}
N = int(sys.argv[1]) if len(sys.argv) > 1 else 600
B2, B4 = bfile(sys.argv[2]) if len(sys.argv) > 2 else {}, bfile(sys.argv[3]) if len(sys.argv) > 3 else {}
bad = 0
for n in range(1, N + 1):
    a, b = least(n, 2), least(n, 4)
    if n in B2 and B2[n] != a: bad += 1; print('A227781 mismatch', n, a, B2[n])
    if n in B4 and B4[n] != b: bad += 1; print('A227784 mismatch', n, b, B4[n])
    ra = 4 if n % 8 == 0 else 3 if n % 8 == 4 else None
    if (ra is not None and a != ra) or (ra is None and a > 2): bad += 1; print('rule2 fails', n, a)
    rb = 15 if n % 16 == 0 else 7 if n % 16 == 8 else None
    if (rb is not None and b != rb) or (rb is None and b > 4): bad += 1; print('rule4 fails', n, b)
print('n <= %d checked, mismatches: %d' % (N, bad))
