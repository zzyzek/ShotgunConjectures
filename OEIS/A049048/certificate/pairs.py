# From sp output: composite c with two n >= 2 needs (a) two primes p != q with
# two common n < min(p,q) in S_p and S_q, or (b) a prime p with two n in S_{p^2}.
import sys, collections
pairmap = collections.defaultdict(list)
sq = []
for line in open(sys.argv[1]):
  p, rest = line.split(':'); p = int(p)
  toks = rest.split()
  S = [int(t.rstrip('*')) for t in toks]
  S2 = [int(t.rstrip('*')) for t in toks if t.endswith('*')]
  if len(S2) >= 2: sq.append((p, S2))
  for i in range(len(S)):
    for j in range(i+1, len(S)):
      pairmap[(S[i], S[j])].append(p)
multi = {k: v for k, v in pairmap.items() if len(v) >= 2}
print("primes", sum(1 for _ in open(sys.argv[1])), "pairs", len(pairmap), "pairs shared by >=2 primes", len(multi))
for k, v in sorted(multi.items())[:20]: print(k, v)
print("p^2 with two n:", sq)
print("max |S_p|:", max((len(l.split())-1, int(l.split(':')[0])) for l in open(sys.argv[1])))
