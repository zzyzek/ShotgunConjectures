# Recaman (UPINT F19): every n>=23 has two partitions n=a+b+c, 0<a<b<c, with equal abc.
# Family: A=(2t+2s, 8t+2s+2w, 9t+3w), B=(3t+3s, 4t+s+w, 12t+4w); both sum 19t+4s+5w,
# both products 12(t+s)(4t+s+w)(3t+w). Choose 0<=s,w<=18 with 4s+5w = n mod 19, t>=37.
def witness(n):
    for s in range(19):
        for w in range(19):
            if (n-4*s-5*w)%19==0:
                t=(n-4*s-5*w)//19
                if t<37: continue
                A=sorted((2*t+2*s,8*t+2*s+2*w,9*t+3*w)); B=sorted((3*t+3*s,4*t+s+w,12*t+4*w))
                return A,B
for n in range(865,200000):
    A,B=witness(n)
    assert sum(A)==n==sum(B) and A[0]*A[1]*A[2]==B[0]*B[1]*B[2] and A!=B
    assert A[0]<A[1]<A[2] and B[0]<B[1]<B[2] and A[0]>0
print("family verified 865..2e5; f19s.py covers n<=1500 (fails only n<=18 and 22)")
