# Look for two-block families m = a*10^k + b (k large) with m^3 - m + e (e = 0, 1) a palindrome
# for all large k (also m = a*10^k - b): need the block values A=a^3, B=3a^2 b, C=3ab^2-a, D=b^3-b+e to form a palindromic
# block string. Tested directly: build m for two values of k and check palindromes.
import sys
R = int(sys.argv[1])
def pal(x):
    s = str(x); return s == s[::-1]
hits = []
for a in range(1, R):
    for b in range(0, R):
        for e, sgn in ((0, 1), (1, 1), (0, -1), (1, -1)):
            ok = True
            for k in (len(str(max(a, b))) * 3 + 3, len(str(max(a, b))) * 3 + 4):
                m = a * 10 ** k + sgn * b
                if not pal(m ** 3 - m + e):
                    ok = False; break
            if ok:
                hits.append((a, sgn * b, e))
print(hits[:50], len(hits))
