\\ A129756: count roots of x^d - x^(d-1) - ... - 1 with Re > 0 (polroots,
\\ 60 digits) for d = 1..120 and compare with 1 + 2*floor((d-1)/4) = A129756(d-1).
\\ Also prints the smallest |Re| over all roots (distance from the imaginary axis).
\\ Run: gp -q -D recover=0 rhp.gp < /dev/null ; expect no MISMATCH and no "***".
default(realprecision,60);
for(d=1,120, P=x^d-sum(i=0,d-1,x^i); r=polroots(P); c=sum(i=1,#r,real(r[i])>0); m=vecmin(vector(#r,i,abs(real(r[i])))); f=1+2*((d-1)\4); if(c!=f, print("MISMATCH d=",d," c=",c," f=",f)); if(d<=12||d%20==0, print(d," ",c," ",f," minRe=",m)));
