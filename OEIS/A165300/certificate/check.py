# OEIS A165300: a(n) = smallest positive number not already in the sequence such that the
# concatenated decimal digits of a(1), ..., a(n) continue the cyclic path 1, 2, 1, 2, ...
# Checks the 25 printed terms, Layman's four rules for n < N, and the closed form
#   a(4j+3) = alt(1, 2j+2), a(4j+4) = alt(1, 2j+3), a(4j+5) = alt(2, 2j+2), a(4j+6) = alt(2, 2j+3),
# with alt(s, l) the l-digit alternating number starting with digit s.
#
import sys
DATA = [1,2,12,121,21,212,1212,12121,2121,21212,121212,1212121,212121,
2121212,12121212,121212121,21212121,212121212,1212121212,12121212121,
2121212121,21212121212,121212121212,1212121212121,212121212121]
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300

def alt(s, l):
  return int("".join(str(s if i % 2 == 0 else 3 - s) for i in range(l)))

seq, used, L = [], set(), 0
for n in range(1, N + 1):
  d = 1 if L % 2 == 0 else 2
  # Candidates are exactly alt(d, l), increasing in l; search by brute force over l.
  #
  l = 1
  while alt(d, l) in used: l += 1
  m = alt(d, l)
  seq.append(m); used.add(m); L += l
assert seq[:len(DATA)] == DATA

# Brute-force definition for the first 12 terms (all integers, no candidate shortcut).
#
pat = lambda i: 1 if i % 2 == 0 else 2
s2, used2, w = [], set(), ""
for n in range(12):
  m = 1
  while True:
    t = w + str(m)
    if m not in used2 and all(int(t[i]) == pat(i) for i in range(len(t))): break
    m += 1
  s2.append(m); used2.add(m); w += str(m)
assert s2 == DATA[:12]

for n in range(1, N):
  x, y = str(seq[n-1]), str(seq[n])
  if   x[0] == "1" and x[-1] == "1" and n > 1: assert y == x[1:]
  elif x[0] == "1" and x[-1] == "2":           assert y == x + "1"
  elif x[0] == "2" and x[-1] == "1":           assert y == x + "2"
  elif x[0] == "2" and x[-1] == "2":           assert y == "1" + x
for j in range(0, (N - 6) // 4):
  assert seq[4*j+2:4*j+6] == [alt(1,2*j+2), alt(1,2*j+3), alt(2,2*j+2), alt(2,2*j+3)]
print("OK: data", len(DATA), "terms; rules and closed form for n <", N)
