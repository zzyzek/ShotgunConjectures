# Deck simulation of FO4C3 (flip top 4 as a unit, then cut 3 from top to bottom); prints a(n), n=4..30.
def move(deck):
  top=[(c,not u) for (c,u) in reversed(deck[:4])]
  d=top+deck[4:]
  return d[3:]+d[:3]
out=[]
for n in range(4,31):
  start=[(i,False) for i in range(n)]; d=move(start); j=1
  while d!=start: d=move(d); j+=1
  out.append(j)
print(out)
# The position map used in A221564_mathlib.lean agrees with the deck move.
def mv(n,p,b):
  if p==0: return (0,not b)
  if p<=3: return (n-p,not b)
  return (p-3,b)
for n in range(4,31):
  d=move([(i,False) for i in range(n)])
  for q,(c,u) in enumerate(d): assert mv(n,c,False)==(q,u)
print("position map ok n=4..30")
