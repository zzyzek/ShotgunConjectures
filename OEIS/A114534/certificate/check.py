# A114534: n x n matrix with entries F(0), F(1), ..., F(n^2-1) row by row; rank 2 (n >= 2).
from sympy import Matrix, fibonacci
print([(n, Matrix(n, n, lambda r, c: fibonacci(r*n + c)).rank()) for n in range(2, 13)])
print("permanent n = 3 check:", Matrix(3, 3, lambda r, c: fibonacci(3*r + c)).per())
