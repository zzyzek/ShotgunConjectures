# OEIS A158233: recompute terms from the definition (A120070 read by rows,
# T(m,l) = m^2 - l^2, offset 2), compare with the entry's DATA, and check
# the residue argument: within a row the product depends only on (m, l)
# mod 9, across rows only on l mod 9.
import sys

def a120070(N):
    out = [None, None]
    m = 2
    while len(out) < N:
        for l in range(1, m):
            out.append(m * m - l * l)
        m += 1
    return out

data = [6,4,3,0,3,6,0,3,0,0,4,0,0,4,6,0,0,6,0,6,0,0,6,3,0,3,6,3,4,0,0,4,0,0,
        4,0,0,6,3,0,3,6,0,0,3,0,0,6,0,6,0,0,3,3,6,4,0,0,4,0,0,4,0,0,4,3,0,3,
        0,0,0,3,0,6,6,0,3,6,0,3,0,0,0,3,0,6,6,0,3,0,0,4,0,0,4,0,0,4,0,0,4,0,0,4,6]
T = a120070(200000)
a = [None] + [(T[n + 1] * T[n + 2]) % 9 for n in range(1, 199990)]
assert a[1:len(data) + 1] == data, "DATA mismatch"
assert set(a[1:]) == {0, 3, 4, 6}, set(a[1:])
row = {((m*m - l*l) * (m*m - (l+1)**2)) % 9 for m in range(9) for l in range(9)}
cross = {((2*l + 1) * ((l + 2)**2 - 1)) % 9 for l in range(9)}
assert row <= {0, 3, 4, 6} and cross <= {0, 3, 4, 6}
print("OK: DATA matches,", len(a) - 1, "terms in {0,3,4,6}; residues row", sorted(row), "cross", sorted(cross))
