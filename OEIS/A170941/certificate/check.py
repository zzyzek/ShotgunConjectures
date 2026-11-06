# A170941 checks (exact integer arithmetic).
# 1. Brute force: involutions of [n] with no adjacent transposition (i i+1),
#    n <= 10, against the recurrence of the entry and the inclusion-exclusion
#    sum b(n) = sum_k (-1)^k C(n-k,k) I(n-2k), I = A000085.
# 2. Recurrence against the entry's data (a(0..27)).
# 3. a(n)/I(n) for a few n, against exp(-1).
#
from math import comb, exp
from fractions import Fraction

def involutions(n):
  # Yield involutions of range(n) as tuples p with p[p[i]] == i.
  #
  p = [-1] * n
  def rec(i):
    while i < n and p[i] != -1:
      i += 1
    if i == n:
      yield tuple(p)
      return
    p[i] = i
    yield from rec(i + 1)
    for j in range(i + 1, n):
      if p[j] == -1:
        p[i], p[j] = j, i
        yield from rec(i + 1)
        p[j] = -1
    p[i] = -1
  yield from rec(0)

N = 500
I = [1, 1]
for n in range(2, N + 1):
  I.append(I[n - 1] + (n - 1) * I[n - 2])
a = [1, 1, 1, 2]
for n in range(4, N + 1):
  a.append(a[n - 1] + (n - 1) * a[n - 2] - a[n - 3] + a[n - 4])
b = [sum((-1) ** k * comb(n - k, k) * I[n - 2 * k] for k in range(n // 2 + 1)) for n in range(N + 1)]
assert a == b, "recurrence != inclusion-exclusion"

for n in range(11):
  c = sum(1 for p in involutions(n) if all(p[i] != i + 1 for i in range(n - 1)))
  assert c == a[n], (n, c, a[n])

data = [1,1,1,2,5,13,37,112,363,1235,4427,16526,64351,259471,1083935,4668704,
        20732609,94607409,443476993,2130346450,10482534517,52740593933,
        271186949333,1423127827792,7618169603035,41554791114643,230857090312059,
        1305086617517534]
assert a[:len(data)] == data

for n in (10, 50, 100, 500):
  print(n, float(Fraction(a[n], I[n])))
print("exp(-1) =", exp(-1))
print("OK: brute force n<=10, a == b for n<=500, data a(0..27)")
