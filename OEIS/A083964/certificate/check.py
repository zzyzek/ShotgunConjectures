# A083964 checks.
# (1) Brute-force least palindromic multiple of k=2n-1 beginning with k, n <= 40,
#     against the OEIS data (search bound 10^8; 0 means none below the bound).
# (2) Zero pattern: for n <= 4090, a(n) = 0 exactly when gcd(k, 10^c) does not divide rev(k)
#     (decided by the Lean theorems except the residual case below).
# (3) Residual case not covered by the Lean theorems: 5^c | rev(k) and 5^(c+1) | k,
#     k a c-digit odd number; enumerated for c <= 30.
from math import gcd
data = [1,3,5,7,9,11,131131,0,174471,1911191,219912,238832,0,27972,2930392,31713,33,0,3701073,393393,
        412214,4357534,0,476674,49294,513315,5305035,55,579975,59295,6188816,6317136,0,6735376,6933396,
        7109017,7305037,0,77,793397]
def rev(k): return int(str(k)[::-1])
def least(k, bound=10**8):
    s = str(k)
    for P in range(k, bound, k):
        t = str(P)
        if t == t[::-1] and t.startswith(s):
            return P
    return 0
for n, d in enumerate(data, 1):
    k = 2 * n - 1
    v = least(k)
    assert v == d, (n, v, d)
print("(1) data n<=40 reproduced")
for n in range(1, 4091):
    k = 2 * n - 1
    c = len(str(k))
    cond = rev(k) % gcd(k, 10 ** c) == 0
    v = 0
    kk = k
    while kk % 5 == 0:
        kk //= 5; v += 1
    assert cond == (k % 5 != 0 or rev(k) % 5 ** v == 0 or (v > c and rev(k) % 5 ** c == 0))
print("(2) characterisation consistent n<=4090")
res = []
for c in range(1, 31):
    step = 5 ** (c + 1)
    for k in range(step, 10 ** c, 2 * step):
        if len(str(k)) == c and rev(k) % 5 ** c == 0:
            res.append(k)
print("(3) residual case c<=30:", res)
