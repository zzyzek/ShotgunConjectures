# A213257/A213258: greedy {x,2x,4x}-free sequence (a(1)=1, a(2)=2) versus
# "n excluded iff v2(n) = 2 mod 3" and the fixed point of 0->01,1->02,2->03,3->01.
#
N = 200000
inset = [False] * (N + 1)
inset[1] = inset[2] = True
for n in range(3, N + 1):
  inset[n] = not (n % 4 == 0 and inset[n // 2] and inset[n // 4])
def v2(n):
  e = 0
  while n % 2 == 0: n //= 2; e += 1
  return e
rule = all(inset[n] == (v2(n) % 3 != 2) for n in range(1, N + 1))
w = [0]
sub = {0: [0, 1], 1: [0, 2], 2: [0, 3], 3: [0, 1]}
while len(w) < N:
  w = [c for x in w for c in sub[x]]
morph = all((w[n - 1] == 2) == (not inset[n]) for n in range(1, N + 1))
print("greedy exclusion == (v2(n) = 2 mod 3) for n <= %d:" % N, rule)
print("excluded n == positions of 2 in the morphism fixed point:", morph)
