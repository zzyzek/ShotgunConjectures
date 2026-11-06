# Brute force: for n = 1..40, all solutions r <= s <= t of r*s*t = n*(r+s+t);
# rs <= 3n bounds r, s; t = n(r+s)/(rs-n). Prints max t, max s and checks the claim.
for n in range(1, 41):
    mt = ms = 0
    for r in range(1, 3 * n + 1):
        for s in range(r, 3 * n // r + 1):
            d = r * s - n
            if d <= 0 or (n * (r + s)) % d: continue
            t = n * (r + s) // d
            if t < s: continue
            assert r * s * t == n * (r + s + t)
            mt, ms = max(mt, t), max(ms, s)
    assert (mt, ms) == (n * (n + 2), 2 * n), n
print("ok n=1..40")
