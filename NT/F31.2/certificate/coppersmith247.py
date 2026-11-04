# Decide: is there m>0 with balanced-ternary digits of m and k*m all nonzero?
# BFS over carries of the multiplication k*m read from least significant digit.
import sys
def bt_zero_free(c):
    while c!=0:
        r=c%3
        if r==0: return False
        c=(c-(1 if r==1 else -1))//3
    return True
def exists(k):
    seen=set(); frontier=[0]; first=True
    while frontier:
        nf=[]
        for c in frontier:
            for d in (1,-1):
                v=k*d+c; r=v%3
                if r==0: continue
                dig=1 if r==1 else -1
                nc=(v-dig)//3
                if bt_zero_free(nc): return True
                if nc not in seen:
                    seen.add(nc); nf.append(nc)
        frontier=nf
    return False
print("247:",exists(247))
bad=[k for k in range(1,3000) if k%3!=0 and not exists(k)]
print(len(bad),bad[:60])
