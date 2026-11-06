# A193550: compute the continued fraction coefficients exactly (integers), compare with the b-file,
# check a(n) = Catalan(n) (mod 4), and check that sqrt((A-1)/x) has integer coefficients.
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 241
def lam(i): return (2 * (i // 2) + 1) ** 2
def inv1(D, N):
    # inverse of a series with D[0] = 1, integer arithmetic
    r = [1] + [0] * (N - 1)
    for n in range(1, N): r[n] = -sum(D[k] * r[n - k] for k in range(1, n + 1))
    return r
T = [1] + [0] * (N - 1)
for j in reversed(range(N + 1)):
    D = [1] + [-lam(j) * T[i] for i in range(N - 1)]
    T = inv1(D, N)
A = T
b = {}
try:
    for l in open('b193550.txt'):
        p = l.split()
        if len(p) == 2: b[int(p[0])] = int(p[1])
except OSError: pass
mism = [n for n in b if n < N and b[n] != A[n]]
cat = [1]
for n in range(1, N): cat.append(cat[-1] * 2 * (2 * n - 1) // (n + 1))
mod4 = [n for n in range(N) if (A[n] - cat[n]) % 4]
F = A[1:]
B = [1]
nonint = []
for n in range(1, len(F)):
    s = F[n] - sum(B[i] * B[n - i] for i in range(1, n))
    if s % 2: nonint.append(n)
    B.append(s // 2)
print('terms', N, 'b-file mismatches', mism, 'a != Catalan mod 4 at', mod4[:5], 'non-integer B at', nonint[:5])
print('B(0..9) =', B[:10])
