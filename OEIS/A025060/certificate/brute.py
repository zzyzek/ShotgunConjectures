# A025060: brute force: every v in [-200, 200] is i*j + j*k + k*i with distinct nonzero |i|,|j|,|k| <= 60.
B=60
reps={}
for i in range(-B,B+1):
  for j in range(i+1,B+1):
    for k in range(j+1,B+1):
      if 0 in (i,j,k): continue
      v=i*j+j*k+k*i
      if -200<=v<=200 and v not in reps: reps[v]=(i,j,k)
print([v for v in range(-200,201) if v not in reps]); print(reps.get(-3), reps.get(-2), reps.get(0), reps.get(-6), reps.get(-8))
