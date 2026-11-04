# UPINT E4 (Erdős's last email): max over primitive A in [1,x] of sum_{n<=x} #{a in A: a<n} = sum (x-a).
# Conjectured x^2/6+O(x). Witness: A=(x/4,x/2] U {odd a in (x/2,3x/4]} gives ~13x^2/64.
for x in [1000,4000,16000]:
    A=[a for a in range(x//4+1,x//2+1)]+[a for a in range(x//2+1,3*x//4+1) if a%2]
    S=set(A); assert all(m not in S for a in A for m in range(2*a,x+1,a))
    v=sum(x-a for a in A); print(x,v,v/x**2,"x^2/6 =",x*x/6,"excess/x =",(v-x*x/6)/x)
