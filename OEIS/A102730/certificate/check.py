# A102730(n) = number of k with bin(k!) a substring of bin(n!).
# Checks: (1) recompute a(0..300) and compare with the OEIS data;
# (2) the lemmas of the proof numerically for L = 3..10:
#   s(x) = odd part of x! mod 2^L;
#   (A) s(2^N a + r) = s(2^N a) s(r) when r < 2^(N-L+1);
#   (B) s(2^N a) = s(a) when 2^L | a;
#   (C) S' = {s(a) : 2^L | a} contains 1 (explicit a = 2^L * sum_{i<J} 2^(iT), J = 2^(L-2));
# (3) the construction n = 2^N a + m gives bin(m!) inside bin(n!) for m = 3..8.
import math, sys
sys.setrecursionlimit(10000)
def odd(x):
    while x % 2 == 0: x //= 2
    return x
def a102730(n):
    s = bin(math.factorial(n))[2:]
    return sum(1 for k in range(n + 1) if bin(math.factorial(k))[2:] in s)
data = [1,2,3,4,5,6,5,6,7,6,7,6,7,6,6,6,7,6,6,6,7,6,7,8,6,7,6,7,6,7,7,7,8,7,7,7,6,8,7,7,7,7,7,8,7,7,6,7,7,7,7,7,7,7,7,8,7,7,7,7,7,7,7,7,8,7,7,7,7,7,7,8,7,7,8,7,7,7,7,7,7,8,7,7,7,7,8,7,7,7,7,8,7,7,8,8,7,7,7,8,8,7,8,7,7]
assert [a102730(n) for n in range(len(data))] == data, "data mismatch"
print("data a(0..%d) reproduced" % (len(data) - 1))
def s_mod(x, L):
    # odd part of x! mod 2^L via Legendre-style product over levels
    M = 1 << L; r = 1
    while x > 0:
        # product of odd numbers <= x, mod M: full periods give 1 (L >= 3)
        q, rem = divmod(x, M)
        p = 1
        for o in range(1, rem + 1, 2): p = p * o % M
        r = r * p % M
        x //= 2
    return r
for L in range(3, 11):
    M = 1 << L
    for x in range(1, 401):
        assert s_mod(x, L) == odd(math.factorial(x)) % M
    for N in range(L, L + 4):
        for a in range(1, 40):
            for r in range(0, 1 << (N - L + 1)):
                assert s_mod((a << N) + r, L) == s_mod(a << N, L) * s_mod(r, L) % M
    for N in range(0, 12):
        for a in range(M, 30 * M, M):
            assert s_mod(a << N, L) == s_mod(a, L)
    J, T = 1 << (L - 2), L + 3
    a = M * sum(1 << (i * T) for i in range(J))
    assert s_mod(a, L) == 1, L
print("lemmas A, B, C hold numerically for L = 3..10")
for m in range(3, 9):
    om = odd(math.factorial(m)); L = max(3, om.bit_length()); M = 1 << L
    J, T = 1 << (L - 2), L + m.bit_length() + 2
    a = M * sum(1 << (i * T) for i in range(J))
    assert s_mod(a, L) == 1
    N = L + m.bit_length()
    n = (a << N) + m
    assert s_mod(n, L) == om % M
    print("m=%d L=%d: n has %d bits; s(n) = odd(m!) mod 2^L" % (m, L, n.bit_length()))
