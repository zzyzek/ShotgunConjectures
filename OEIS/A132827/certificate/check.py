# A132827: compare the entry's data, the entry's FORMULA (b = A005206) and the
# dispersion of f(n) = floor(n*phi + n + 1), all in exact integer arithmetic.
from math import isqrt
def fl_phi(n): return (n + isqrt(5*n*n)) // 2
def f(n): return fl_phi(n) + n + 1
G = [0]
for n in range(1, 3000): G.append(n - G[G[n-1]])
F = [0, 1]
for _ in range(120): F.append(F[-1] + F[-2])
def form(i, j, b): return (b(i)+1)*F[2*j] + (i-b(i))*F[2*j+1]
bG  = lambda i: G[i]
bOK = lambda i: 2*i - fl_phi(i)
R = 2000
rng = set(f(n) for n in range(1, 4*R))
comp = [m for m in range(1, 3*R) if m not in rng][:R]
assert comp == [fl_phi(i) + 1 for i in range(R)]
def disp(i, j):
    x = comp[i]
    for _ in range(j-1): x = f(x)
    return x
data = [1,3,2,8,6,4,21,16,11,5,55,42,29,14,7,144,110,76,37,19,9,377,288,199,
        97,50,24,10,987,754,521,254,131,63,27,12]
anti = [(i, s-i+1) for s in range(8) for i in range(s+1)][:36]
assert [disp(i, j) for i, j in anti] == data
assert [form(i, j, bOK) for i, j in anti] == data
bad = [(i, j) for i, j in anti if form(i, j, bG) != data[anti.index((i, j))]]
print("entry FORMULA (A005206) differs from data at", bad)
assert all(form(i, j, bOK) == disp(i, j) for i in range(R) for j in range(1, 15))
assert all(form(i, 1, bG) != disp(i, 1) for i in range(4, R))
print("dispersion = closed form for i <", R, ", j <= 14; A005206 formula wrong for every row i >= 4 (i <", R, ")")
