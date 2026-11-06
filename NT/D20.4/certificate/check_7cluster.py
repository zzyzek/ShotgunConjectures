from itertools import combinations
from math import isqrt
P=[(0,0),(374400,-2230800),(1081600,-1488240),(-453024,-1630200),(426725,-1630200),(569088,-1291680),(-439040,-1308720)]
ok=True
D=[]
for i in range(7):
  row=[]
  for j in range(7):
    d2=(P[i][0]-P[j][0])**2+(P[i][1]-P[j][1])**2; d=isqrt(d2); ok&=d*d==d2; row.append(d)
  D.append(row)
for a,b,c in combinations(P,3):
  ok&=((b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0]))!=0
def det4(q):
  import fractions
  M=[[x*x+y*y,x,y,1] for x,y in q]
  def det(M):
    if len(M)==1: return M[0][0]
    return sum((-1)**j*M[0][j]*det([r[:j]+r[j+1:] for r in M[1:]]) for j in range(len(M)))
  return det(M)
for q in combinations(P,4): ok&=det4(q)!=0
print(ok, max(max(r) for r in D)); print(D)
