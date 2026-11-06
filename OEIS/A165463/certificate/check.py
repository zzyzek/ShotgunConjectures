# Jacobi-bridge identities (A165460, A165605, A165462, A165463): direct computation.
import sys
def jacobi(a, n):
    a %= n; r = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5): r = -r
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3: r = -r
        a %= n
    return r if n == 1 else 0
def S(m, N): return sum(jacobi(i, m) for i in range(N + 1))
N = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
bad = 0
A460 = [S(12 * n + 7, 4 * n + 2) for n in range(N)]
A605 = [S(12 * n + 7, 6 * n + 3) for n in range(N)]
for n in range(N):
    if n % 2 == 0 and A460[n] != 2 * A605[n]: bad += 1
    if n % 2 == 1 and 3 * A460[n] != 2 * A605[n]: bad += 1
print('A165460(0..9) =', A460[:10], ' A165605(0..9) =', A605[:10])
print('n <', N, 'identity failures:', bad)
print('A165463 start:', [12 * n + 7 for n in range(N) if A460[n] == 0][:8])
print('A165462 start:', [3 * n + 1 for n in range(N) if A460[n] == 0][:8])
