# Checks (exact integers) for OEIS A152718 / A054393:
# 1. walk DP w (as in the Lean file) == Alcover's matrix power (M^n)[1,1] with the n x n
#    matrix M_ij = 1 iff j < i, or i == j <= 5, or j == i+1   (n <= 40);
# 2. DP == OEIS A054393 data (b-file if given, else listed terms);
# 3. A152718 recurrence == OEIS data / b-file;
# 4. sum_k a152718(k) [x^n] z^k == a054393(n), z = x(1+z+z^2), n <= NMAX;
# 5. mot(n+1) == Motzkin(n).
import sys
NMAX = 150
def dp(N):
    w = [1] + [0]*N; out = [1]
    for n in range(N):
        w = [(w[j-1] if j > 0 else 0) + (w[j] if j <= 4 else 0) + sum(w[j+1:n+1]) for j in range(N+1)]
        out.append(w[0])
    return out
def matpow(n):
    if n == 0: return 1
    M = [[1 if (j < i or (i == j and i <= 5) or j == i+1) else 0 for j in range(1, n+1)] for i in range(1, n+1)]
    v = [1] + [0]*(n-1)
    for _ in range(n): v = [sum(v[i]*M[i][j] for i in range(n)) for j in range(n)]
    return v[0]
a = dp(NMAX)
assert all(a[n] == matpow(n) for n in range(41)), "matrix mismatch"
b = [1,1,1,1,2,4]
while len(b) <= NMAX: b.append(2*b[-1]-b[-2]+2*b[-3]-b[-4]+b[-5])
def bfile(path):
    d = {}
    for line in open(path):
        s = line.split()
        if len(s) == 2 and not line.startswith('#'): d[int(s[0])] = int(s[1])
    return d
if len(sys.argv) > 2:
    A, B = bfile(sys.argv[1]), bfile(sys.argv[2])
    na = sum(1 for n in A if n <= NMAX); nb = sum(1 for n in B if n <= NMAX)
    assert all(A[n] == a[n] for n in A if n <= NMAX), "A054393 b-file mismatch"
    assert all(B[n] == b[n] for n in B if n <= NMAX), "A152718 b-file mismatch"
    print("b-files agree on", na, "and", nb, "terms")
t = [[0]*(NMAX+2) for _ in range(NMAX+1)]; t[0][0] = 1
for n in range(NMAX):
    for k in range(1, NMAX+1): t[n+1][k] = t[n][k-1] + t[n][k] + t[n][k+1]
assert all(sum(b[k]*t[n][k] for k in range(n+1)) == a[n] for n in range(NMAX+1)), "transform mismatch"
mot = [0]
for n in range(NMAX): mot.append((1 if n == 0 else 0) + mot[n] + sum(mot[i]*mot[n-i] for i in range(n+1)))
motz = [1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188, 5798]
assert mot[1:13] == motz and all(mot[n] == t[n][1] for n in range(NMAX+1))
print("all checks passed up to n =", NMAX)
