# A047926: C(N) = #{0<a<=b<=c : a^2+b^2+c^2 = N}; P(n) = primitive (not all divisible by 3)
# sorted representations of 9^n; r3 = signed ordered count. Checks C(9^(n+1)) = a(n),
# 2P(n) = 3^(n-1)+1 and r3(9^n) = 6(2*3^n - 1) for n <= NMAX.
import sys, math
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 7
def reps(N):
    out = []; r = math.isqrt(N)
    for x in range(1, r + 1):
        for y in range(x, r + 1):
            z2 = N - x * x - y * y
            if z2 < y * y: break
            z = math.isqrt(z2)
            if z * z == z2: out.append((x, y, z))
    return out
def r3(N):
    tot = 0; r = math.isqrt(N)
    for x in range(-r, r + 1):
        for y in range(-r, r + 1):
            z2 = N - x * x - y * y
            if z2 < 0: continue
            z = math.isqrt(z2)
            if z * z == z2: tot += 1 if z == 0 else 2
    return tot
for n in range(1, NMAX + 1):
    R = reps(9 ** n); P = sum(1 for t in R if not all(v % 3 == 0 for v in t))
    a = (3 ** n + 2 * (n - 1) + 1) // 4
    line = f"n={n} C(9^n)={len(R)} a(n-1)={a} P={P} (3^(n-1)+1)/2={(3**(n-1)+1)//2}"
    if n <= 5: line += f" r3={r3(9 ** n)} 6(2*3^n-1)={6*(2*3**n-1)}"
    print(line)
