# Count n <= X with sigma(n) = n (mod 10), with 10 | n, and with 10 not dividing sigma(n).
import sys
X=int(sys.argv[1])
sig=[0]*(X+1)
for d in range(1,X+1):
  for m in range(d,X+1,d): sig[m]+=d
cnt=0; mult10=0; bad=0; k=0
for n in range(1,X+1):
  if sig[n]%10==n%10: cnt+=1
  if sig[n]%10: bad+=1
  if n in (10**3,10**4,10**5,10**6,10**7) or n==X:
    print("X=%d  #{sigma(n)=n mod 10}=%d  ratio X/count=%.5f  #{10 not | sigma(n)}/X=%.5f"%(n,cnt,n/cnt,bad/n))
