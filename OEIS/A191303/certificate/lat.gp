\\ M x = 0 for x = (a_1,e_1,...,a_k,e_k): coefficients of t^0..t^k of
\\ sum_i (a_i t + e_i)(b^(k-i) - c^(i-1)), b = al t + be, c = b + d.
sysmat(k,al,be,d)={my(M=matrix(k+1,2*k),b=al*'t+be,c=b+d,w);
  for(i=1,k, w=b^(k-i)-c^(i-1);
    for(p=0,k, M[p+1,2*i]=polcoeff(w,p,'t); if(p>=1, M[p+1,2*i-1]=polcoeff(w,p-1,'t))));M}
\\ expected number of a-vectors in the box [0,al]^k on the lattice of a-projections
expct(k,al,be,d)={my(K=matkerint(sysmat(k,al,be,d)),A,r,G);
  A=vecextract(K,vector(k,i,2*i-1),"..");  A=mathnf(A); r=#A;
  G=A~*A; [r, (al+1.)^r/sqrt(matdet(G))]}
