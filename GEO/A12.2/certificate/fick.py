import math, random
def tri(h=12.0,b=5.0): return [(-b,0.0),(b,0.0),(0.0,h)]
def place(T,th,dx,dy):
    c,s=math.cos(th),math.sin(th); return [(c*x-s*y+dx,s*x+c*y+dy) for x,y in T]
def halfplanes(T):
    # ccw triangle: inside = left of each edge
    H=[]
    for i in range(3):
        (x1,y1),(x2,y2)=T[i],T[(i+1)%3]
        H.append((x1,y1,x2-x1,y2-y1))
    return H
def clip_len(p,q,T):
    t0,t1=0.0,1.0
    for (x1,y1,ex,ey) in halfplanes(T):
        # f(t) = cross(e, P(t)-A) >= 0
        f0=ex*(p[1]-y1)-ey*(p[0]-x1); f1=ex*(q[1]-y1)-ey*(q[0]-x1); d=f1-f0
        if abs(d)<1e-15:
            if f0<0: return 0.0
            continue
        t=-f0/d
        if d>0: t0=max(t0,t)
        else: t1=min(t1,t)
    return max(0.0,t1-t0)*math.dist(p,q)
def L(A,B): return sum(clip_len(A[i],A[(i+1)%3],B) for i in range(3))
def ratio(x,T):
    B=place(T,*x); a=L(T,B); b=L(B,T)
    return a/b if b>1e-9 and a>1e-9 else 0
if __name__=="__main__":
    T=tri(); psi=2*math.asin(5/13); print("psi deg",math.degrees(psi),"1/sin(psi/2)",13/5)
    random.seed(1); best=(0,None)
    for rep in range(400):
        x=[random.uniform(0,2*math.pi),random.uniform(-8,8),random.uniform(-6,14)]; f=ratio(x,T); st=1.0
        for it in range(3000):
            y=[x[0]+random.gauss(0,st*0.3),x[1]+random.gauss(0,st),x[2]+random.gauss(0,st)]; g=ratio(y,T)
            if g>f: x,f=y,g
            if it%300==299: st*=0.6
        if f>best[0]: best=(f,x)
    print(best)
