def F(s):
  m = max(s); return tuple(s.count(i) for i in range(m+1))
def a_vec(s):
  seen = [s]
  while True:
    s = F(s)
    if s in seen: return seen.index(s)
    seen.append(s)
def a(n): return a_vec(tuple(int(c) for c in bin(n)[2:]))
print([a(n) for n in range(0, 40)])
# pre for pairs
for z in range(0, 12):
  print(z, [a_vec((z, o)) for o in range(1, 14)])
# periodic vectors
cyc=set()
for z in range(0,30):
  for o in range(0,30):
    if z+o==0: continue
    s=(z,o); seen=[s]
    while True:
      s=F(s)
      if s in seen:
        i=seen.index(s); cyc.update(seen[i:]); break
      seen.append(s)
print(sorted(cyc))
bad=[n for n in range(10,1<<16) if a(n)%2==0]; print("even a(n), 10<=n<65536:", bad[:10])
