# Direct simulation of A068638 (greedy) up to X; checks the data and that the odd terms
# are 1 and 25, and that each even term e > 25 satisfies e+1, e+25 composite (and conversely).
import sys
from sympy import isprime
X = int(sys.argv[1])
S = [1]
for y in range(2, X + 1):
    if isprime(y): continue
    if all(not isprime(y + s) for s in S): S.append(y)
data = [1,8,14,20,24,25,26,32,38,44,50,56,62,68,74,80,86,90,92,94,98,104,110,116,118,120,122,128,134,140,144,146,152,158,160,164,170,176,182,184,188,194,200,206,212,218,220,224,230,234,236,242,248,254,260,264,266]
print('data ok', S[:len(data)] == data)
print('odd terms', [s for s in S if s % 2])
E = [e for e in range(26, X + 1, 2) if not isprime(e + 1) and not isprime(e + 25)]
print('evens match', [s for s in S if s % 2 == 0 and s > 25] == E)
