# A084043 / A084044: brute-force least palindromic multiples for n <= 45 (n not divisible by 10),
# compared with the OEIS data; multiples of 10 get 0.
import sys
D43 = [111,222,333,444,555,666,777,888,999,0,1111,82128,41314,414414,55155,61616,317713,41814,41914,0,
       912219,2222,52325,2324232,52525,82628,82728,828828,52925,0,2131312,23232,3333,2243422,535535,
       2136312,43734,88388]
D44 = [1,2,3,4,5,6,7,8,9,0,11,2112,31213,41314,5115,61216,71417,8118,41914,0,12621,22,32223,4224,525,
       26962,27972,82628,52925,0,31713,23232,33,2243422,53235,6336,43734,83638,93639,0,412214,42924,
       34443,44,5445]
def least(n, sandwich):
  if n % 10 == 0: return 0
  s = str(n); P = n
  while True:
    t = str(P)
    if t == t[::-1]:
      if (sandwich and s in t[1:-1]) or (not sandwich and s in t): return P
    P += n
bad = 0
for i, v in enumerate(D43):
  if least(i+1, True) != v: bad += 1; print("A084043", i+1)
for i, v in enumerate(D44):
  if least(i+1, False) != v: bad += 1; print("A084044", i+1)
print("failures:", bad); sys.exit(1 if bad else 0)
