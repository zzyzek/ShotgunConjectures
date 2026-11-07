# Second-reader check: Watanabe's 47 squarefree semiprimes have reciprocal sum 1.
from fractions import Fraction as F
from sympy import factorint
S = [6,10,14,15,21,22,26,33,34,35,38,39,46,51,55,57,58,62,65,69,74,82,85,86,87,91,93,95,
     106,111,123,133,145,155,159,185,203,215,253,265,287,319,493,583,731,851,1073]
assert len(S) == 47 and len(set(S)) == 47
assert all(sorted(factorint(d).values()) == [1, 1] for d in S)
assert sum(F(1, d) for d in S) == 1
print("OK: 47 distinct squarefree semiprimes, reciprocal sum 1")
