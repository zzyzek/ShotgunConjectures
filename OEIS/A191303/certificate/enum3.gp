read("lat.gp");
\\ Generic HNF enumeration: pivot row of column j = largest row index with H[row,j] != 0.
rec3(H,P,K,A,k,al,be,d,i,z)={
  if(i==0,
    my(a=H*z, x, e, ok=1); if(a[1]<1, return(0));
    for(j=1,k, if(a[j]<0||a[j]>al, return(0)));
    x=matinverseimage(A,a); e=vecextract(K,vector(k,j,2*j),"..")*x;
    if(denominator(e)!=1, return(0));
    for(j=1,k, if((a[j]==0&&e[j]<0)||(a[j]==al&&e[j]>be-1),ok=0;break));
    if(ok, print("HIT k=",k," al=",al," be=",be," d=",d," a=",a~," e=",e~); return(1)); return(0));
  my(row=P[i], s=sum(j=i+1,#z,H[row,j]*z[j]), p=H[row,i], lo, hi);
  if(p>0, lo=ceil((0-s)/p); hi=floor((al-s)/p), lo=ceil((al-s)/p); hi=floor((0-s)/p));
  for(t=lo,hi, z[i]=t; if(rec3(H,P,K,A,k,al,be,d,i-1,z), return(1)));
  z[i]=0; 0}
findk3(k,AL,DD,AL0=1)={for(al=AL0,AL,for(d=1,DD,for(be=2-al,al,
  my(K=matkerint(sysmat(k,al,be,d)),A,H,P,r);
  A=vecextract(K,vector(k,i,2*i-1),"..");
  H=mathnf(A); r=#H;
  P=vector(r,j, my(q=0); for(i=1,k, if(H[i,j]!=0, q=i)); q);
  for(j=2,r, if(P[j]<=P[j-1], error("pivot order")));
  for(j=1,r, for(l=1,j-1, if(H[P[j],l]!=0, error("not triangular"))));
  if(rec3(H,P,K,A,k,al,be,d,r,vector(r)~), return([al,be,d]))))); 0}
