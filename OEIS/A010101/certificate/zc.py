# Z-channel (single asymmetric error) conflict graph on binary words of
# length n. Two words conflict when their asymmetric distance
# max(N(x,y), N(y,x)) is at most 1, where N(x,y) counts positions with
# x = 1, y = 0. A code correcting one asymmetric error is an independent set.
#
import gzip

def conflict(x, y):
  a = bin(x & ~y).count('1')
  b = bin(y & ~x).count('1')
  return (x != y) and (max(a, b) <= 1)

def edges(n):
  E = set()
  for x in range(1 << n):
    # Neighbours: flip one bit, or swap a 1 and a 0.
    #
    for i in range(n):
      y = x ^ (1 << i)
      E.add((min(x, y), max(x, y)))
      for j in range(n):
        if ((x >> i) & 1) and not ((x >> j) & 1):
          y = x ^ (1 << i) ^ (1 << j)
          E.add((min(x, y), max(x, y)))
  return E

def load_dimacs(path):
  E = set()
  for l in gzip.open(path, 'rt'):
    t = l.split()
    if t and (t[0] == 'e'):
      a, b = int(t[1]) - 1, int(t[2]) - 1
      E.add((min(a, b), max(a, b)))
  return E

if __name__ == '__main__':
  import sys
  for n in (9, 10, 11, 12):
    mine = edges(n)
    assert all(conflict(a, b) for a, b in mine)
    theirs = load_dimacs(sys.argv[1] + '/1zc.%d.txt.gz' % (1 << n))
    print(n, len(mine), len(theirs), mine == theirs)
