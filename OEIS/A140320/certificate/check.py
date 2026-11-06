# OEIS A140320: a(n) = A137576((3^n-1)/2), A137576(n) = A002326(n)*A006694(n)+1,
# A002326(n) = multiplicative order of 2 mod 2n+1, A006694(n) = number of
# cyclotomic cosets {x*2^k mod 2n+1} with 1 <= x <= 2n (the coset of 0
# excluded, matching the data and a(0) = 0).  Computed from these
# definitions; compared with the A137576 and A140320 DATA and 2n*3^(n-1)+1.

def ordmod2(m):
    if m == 1:
        return 1
    k, v = 1, 2 % m
    while v != 1:
        v = v * 2 % m
        k += 1
    return k

def cosets(m):
    seen, c = set(), 0
    for x in range(1, m):
        if x in seen:
            continue
        c += 1
        y = x
        while y not in seen:
            seen.add(y)
            y = y * 2 % m
    return c

def a137576(n):
    return ordmod2(2 * n + 1) * cosets(2 * n + 1) + 1

d137576 = [1,3,5,7,13,11,13,17,17,19,31,23,41,55,29,31,41,61,37,49,41,43,85,47,
           85,57,53,81,73,59,61,73,73,67,111,71,73,141,151,79,217,83,89,113,89,
           109,131,145,97,211,101,103,169,107,109,145,113,221,133,193,221,141,301,127]
assert [a137576(n) for n in range(len(d137576))] == d137576
d140320 = [1,3,13,55,217,811,2917,10207,34993,118099,393661,1299079,4251529]
for n in range(14):
    v = a137576((3**n - 1) // 2)
    f = 2 * n * 3**(n - 1) + 1 if n else 1
    assert v == f, (n, v, f)
    if n < len(d140320):
        assert v == d140320[n]
print("OK: A137576 data (64 terms), A140320 n = 0..13 = 2n*3^(n-1)+1, data n = 0..12")
