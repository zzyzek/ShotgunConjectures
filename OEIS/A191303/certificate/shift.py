# Convert HIT lines (b = al t + be, digits a_i t + e_i) to s = t - t0 >= 0 with all digits valid,
# verify the identity exactly, print Lean-ready data.
import re, sys
from sympy import symbols, expand, Poly
s = symbols('s')
for line in open('hits.txt'):
    k, al, be, d = map(int, re.findall(r'k=(-?\d+) al=(-?\d+) be=(-?\d+) d=(-?\d+)', line)[0])
    a = list(map(int, re.search(r'a=\[([^\]]*)\]', line).group(1).split(',')))
    e = list(map(int, re.search(r'e=\[([^\]]*)\]', line).group(1).split(',')))
    t0 = 0
    while True:
        b = al * t0 + be
        dig = [a[i] * t0 + e[i] for i in range(k)]
        if b >= 2 and all(0 <= x < b for x in dig) and dig[0] > 0 and dig[-1] > 0: break
        t0 += 1
    B = al * s + (al * t0 + be); C = B + d
    D = [a[i] * s + (a[i] * t0 + e[i]) for i in range(k)]
    L = expand(sum(D[i] * B**(k - 1 - i) for i in range(k)))
    R = expand(sum(D[i] * C**i for i in range(k)))
    assert L == R
    # validity for all s >= 0: digits at s = 0 valid and slopes a_i <= al (equality needs const < b const)
    for i in range(k):
        assert 0 <= a[i] <= al
        if a[i] == al: assert a[i] * t0 + e[i] < al * t0 + be
    print(k, 'b =', B, '| c =', C, '| digits', D, '| deg', Poly(L, s).degree(), '| P =', L)
