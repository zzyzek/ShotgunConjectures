def stab(a,b1,LIM=10**6):
  b=b1
  for n in range(1,LIM):
    # b = b(n); stable if b = x(n+a+1) with 0<=x<n+a
    if n+a>0 and b%(n+a+1)==0 and b//(n+a+1) < n+a: return n,b//(n+a+1)
    b=b+b%(n+a)
for a,b1,x in [(0,1,97),(1,1,97),(2,1,97),(3,1,1),(4,1,3),(5,1,3),(6,1,6),(97,1,43),(0,11,2)]:
  print(a,b1,x,stab(a,b1))
