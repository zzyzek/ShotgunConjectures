# A072939: for 1 <= n < 20000, iterate c for 4n+200 steps; the two-step pattern
# "descending pair with odd gap" (divergence) or reaching (1,1) is detected, and
# compared with: n - 1 > 0 has odd 2-adic valuation (A036554 + 1).
def step(a, b):
    return (a + b) // 2 if (a - b) % 2 == 0 else abs(b - 2 * a)
def classify(n):
    a, b = 1, n
    for _ in range(4 * n + 200):
        if (a, b) == (1, 1):
            return False
        if a > b and (a - b) % 2 == 1:
            return True
        a, b = b, step(a, b)
    raise RuntimeError(n)
def v2(m):
    v = 0
    while m % 2 == 0:
        m //= 2; v += 1
    return v
for n in range(1, 20000):
    assert classify(n) == (n > 1 and v2(n - 1) % 2 == 1), n
print("ok")
