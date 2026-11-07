# A103910: invert the Fibonomial triangle A010048 (rows 0..N), compare with
# the entry data, and test that rows 1..N sum to 0.
from fractions import Fraction
N = 30
F = [0, 1]
while len(F) < N + 3: F.append(F[-1] + F[-2])
def fibonomial(n, k):
    num = den = 1
    for i in range(k): num *= F[n - i]; den *= F[i + 1]
    assert num % den == 0
    return num // den
A = [[fibonomial(i, j) if j <= i else 0 for j in range(N + 1)] for i in range(N + 1)]
# forward substitution: T = A^{-1}, unit lower triangular
T = [[0] * (N + 1) for _ in range(N + 1)]
for i in range(N + 1):
    T[i][i] = 1
    for j in range(i - 1, -1, -1):
        T[i][j] = -sum(T[i][k] * A[k][j] for k in range(j + 1, i + 1))
data = [1,-1,1,0,-1,1,1,0,-2,1,-1,3,0,-3,1,-6,-5,15,0,-5,1,35,-48,-40,60,0,-8,1,181,455,-624,-260,260,0,-13,1,-6056,3801,9555,-6552,-1820,1092,0,-21,1,-3741,-205904,129234,162435,-74256,-12376,4641,0,-34,1]
flat = [T[i][j] for i in range(N + 1) for j in range(i + 1)]
assert flat[:len(data)] == data
assert all(sum(T[i]) == (1 if i == 0 else 0) for i in range(N + 1))
print("OK data", len(data), "terms; row sums rows 0..%d" % N)
