# Check A138904 definition against OEIS data and both conjectures for lengths L <= 16.
import sys
def sym(m):
    s = bin(m)[2:]; L = len(s)
    return sum(1 for k in range(L) if s[k:]+s[:k] == s)
data = [1,1,1,2,1,1,1,3,1,1,2,1,1,1,1,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,5,1,1,1,1,2,1,1,1,1,1,3,1,1,2,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
assert [sym(m) for m in range(0, len(data))] == data
def isprime(d): return d > 1 and all(d % k for k in range(2, d))
for L in range(1, 17):
    vals = {sym(m) for m in range(2**(L-1), 2**L)}
    assert vals == {e for e in range(1, L+1) if L % e == 0}, L
    for d in range(2, L):
        if L % d == 0 and isprime(d):
            R = sum(2**(j*d) for j in range(L//d))
            lhs = {m for m in range(2**(L-1), 2**L) if sym(m) == L//d}
            rhs = {R*a for a in range(2**(d-1), 2**d - 1)}
            assert lhs == rhs, (L, d)
    assert [m for m in range(2**(L-1), 2**L) if sym(m) == L] == [2**L-1]
print("ok")
