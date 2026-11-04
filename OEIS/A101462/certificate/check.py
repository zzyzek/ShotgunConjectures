# A101462: prime(42228) = 509203, and 2^k - 509203 (k >= 19) always has a factor in
# {3, 5, 7, 13, 17, 241}; direct check for 19 <= k <= 3000.
#
N = 510000
s = bytearray([1]) * N; s[0] = s[1] = 0
for i in range(2, 715):
  if s[i]: s[i*i::i] = bytearray(len(range(i*i, N, i)))
print("509203 prime:", bool(s[509203]), " pi(509203) =", sum(s[:509204]))
print("2^18 < 509203 < 2^19:", 2**18 < 509203 < 2**19)
print("covered 19 <= k <= 3000:", all(any((2**k - 509203) % q == 0 for q in (3, 5, 7, 13, 17, 241)) for k in range(19, 3001)))
