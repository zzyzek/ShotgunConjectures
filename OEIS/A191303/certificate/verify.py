import sys, ast
from sympy import symbols, expand
t = symbols('t')
for line in open(sys.argv[1]):
    if line.startswith('none'): continue
    p = line.split(' ', 4); k, al, be, d = map(int, p[:4]); x = ast.literal_eval(p[4])
    b = al*t + be; c = b + d
    m = [x[2*i]*t + x[2*i+1] for i in range(k)]
    lhs = expand(sum(m[i]*b**(k-1-i) for i in range(k))); rhs = expand(sum(m[i]*c**i for i in range(k)))
    print(k, 'identity', expand(lhs - rhs) == 0, 'b =', b, 'c =', c, 'digits', m, 'm(t) =', lhs)
