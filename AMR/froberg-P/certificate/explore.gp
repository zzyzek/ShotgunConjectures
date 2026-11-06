M(p) = matrix(p,p,i,j, if(i==1, if(j==1,Mod(1,p),Mod(0,p)), Mod(i-1,p)^(j-1)));
{
forprime(p=3, 43, my(A=M(p), cp=charpoly(A), mp=minpoly(A), F=factormod(lift(cp),p));
  print(p, " cp=mp:", cp==mp, " degs:", vector(#F~,k,[poldegree(F[k,1]),F[k,2]]), " det:", matdet(A), " tr:", trace(A));
  print("   lin roots:", select(r->r!="", vector(#F~,k, if(poldegree(F[k,1])==1, -polcoef(F[k,1],0), "")))));
}
