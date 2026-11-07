inv=[0]+[pow(d,-1,11) for d in range(1,11)]
def todig(n):
  s=[]
  while n: s.append(n%11); n//=11
  return s[::-1]
def fromdig(L):
  n=0
  for d in L: n=n*11+d
  return n
def step(n):
  L=todig(n); h=[inv[d] for d in L if d]
  return n+fromdig(h)
def show(n): return ''.join('0123456789A'[d] for d in todig(n))
if __name__=='__main__':
  n=1
  for i in range(20): print(show(n)); n=step(n)
  for a in [0,1,2]:
    for b in [0,1,2]:
      for fam in ('43','54'):
        s='1'+fam[0]*a+fam[1]+'84'*b
        n=int(s,11); seq=[s]
        for i in range(6): n=step(n); seq.append(show(n))
        print(fam,a,b,seq)
