import sys
sys.argv=[sys.argv[0]]+sys.argv[1:]
exec(open('smn.py').read().split("n=int(sys.argv[1])")[0])
n=int(sys.argv[1]); 
for m in range(int(sys.argv[2]),int(sys.argv[3])+1):
  lo={4:40*m-1}.get(n,1)
  r=solve(m,n,lo)[0]
  print(m, "s=40m-1 SAT" if r else "s=40m-1 UNSAT", flush=True)
  if r:
    print(m, "s(m,4) =", smn(m,n,lo+1), flush=True)
