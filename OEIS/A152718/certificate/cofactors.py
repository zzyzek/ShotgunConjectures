# Generate linear_combination cofactors for the U/R identities (X = z*v).
# Relations: hv: u*v = 1, hp: (1+z)*p = 1, hq: Q*q = 1.
import sympy as sp
z,v,p,q,X = sp.symbols('z v p q X')
u = 1+z+z**2
Q = 1-2*z+z**2-2*z**3+z**4-z**5
rels = [(v, u, 'hv'), (p, 1+z, 'hp'), (q, Q, 'hq')]
def U(j):
    return [u*(1-2*z+z**2-z**3)*q, u*(1-z-z**3)*q, u**2*(1-z)*q, u**2*q][j] if j < 4 else u**3*q*(u*p)**(j-4)
def Rt(k): return u**3*q*(u*p)**(k+1)*(1+z)
def R(j):
    if j >= 4: return Rt(j-4)
    return U(j+1) + X*R(j+1)
def cof(f):
    # returns dict name->cofactor with f == sum c*(P*var-1), exact
    f = sp.expand(f); cs = {}
    for var, P, name in rels:
        m = sp.degree(f, var)
        if m <= 0: continue
        fk = sp.Poly(f, var).all_coeffs()[::-1]
        S = lambda k: sum((P*var)**i for i in range(k))
        F = sum(fk[k]*P**(m-k) for k in range(m+1))
        c = var**m*sum(fk[k]*P**(m-k)*S(k) for k in range(m+1)) - f*S(m)
        # f = var^m F + (P var - 1)*c ; carry var^m into later cofactors
        for kname in cs: cs[kname] = cs[kname]  # already exact on earlier part
        cs[name] = sp.expand(c)
        # remaining: var^m * F ; recurse on F and multiply cofactors by var^m
        sub = cof(F)
        for kname, kc in sub.items(): cs[kname] = sp.expand(cs.get(kname,0) + var**m*kc)
        return cs
    assert sp.expand(f) == 0, f
    return cs
def check(name, f):
    f = sp.expand(f.subs(X, z*v))
    cs = cof(f)
    P = {n: Pp*var-1 for var,Pp,n in rels}
    assert sp.expand(f - sum(cs[n]*P[n] for n in cs)) == 0
    s = ' + '.join('(%s) * %s' % (sp.sstr(cs[n]).replace('**','^'), n) for n in cs)
    print(name, ':', len(s)); open('lc_%s.txt' % name,'w').write(s)
check('E0', U(0) - (1 + X*U(0) + X**2*R(0)))
for j in range(1,5): check('E%d'%j, U(j) - (U(j-1) + X*U(j) + X**2*R(j)))
check('core1', u*p - (1 + X**2*(u*p)**2*(1+z)))
check('core2', (1+z) - (1 + X*(u*p)*(1+z)))
check('B', U(0) - (1-z-2*z**3-z**5)*q)
