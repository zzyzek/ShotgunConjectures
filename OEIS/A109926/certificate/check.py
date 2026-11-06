# A109926: least k with exactly n values r >= 0 such that k - 2^r is prime.
# Recomputes a(0..12) from that definition and checks residues mod 30.
def primes_upto(N):
    s = bytearray([1])*(N+1); s[0] = s[1] = 0
    for i in range(2, int(N**0.5)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return s
N = 100000
P = primes_upto(N)
def reps(k):
    c, r = 0, 0
    while (1 << r) < k:
        c += P[k - (1 << r)]; r += 1
    return c
first = {}
for k in range(1, N):
    first.setdefault(reps(k), k)
data = [1,3,4,15,21,45,75,465,1095,2145,4935,14955,80685,229845,1295325,1575285,
        9700575,20435415,15054105,53999715,2282745465]
assert [first[n] for n in range(13)] == data[:13]
assert all(k % 2 == 1 for k in range(1, N) if reps(k) >= 3)
print("a(0..12) reproduced; every k <", N, "with >= 3 representations is odd")
print("data mod 30:", [d % 30 for d in data])
