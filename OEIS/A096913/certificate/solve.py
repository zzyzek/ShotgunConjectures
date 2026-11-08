# All k = s^2 with k + (max digit)^(min digit) = t^2.
# d = a^b with 0 <= b <= a <= 9 (0^0 = 1); t = s + j, d = j(2s + j).
sols = set(); cands = 0
for a in range(10):
    for b in range(a + 1):
        d = a ** b
        if d == 0: continue
        j = 1
        while j * j <= d:
            if d % j == 0 and (d // j - j) % 2 == 0:
                s = (d // j - j) // 2
                cands += 1
                ds = [int(c) for c in str(s * s)]
                if max(ds) == a and min(ds) == b:
                    sols.add(s * s)
            j += 1
print(sorted(sols), cands)
