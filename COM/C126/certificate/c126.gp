f(P,M)=
{
  for(m=1,M,
    my(x=P+5^m, n=0, r);
    while(x%6==0,
      x=x/6; n++;
      if(ispseudoprime(x) || (ispower(x,,&r) && ispseudoprime(r)), return([m,n]))));
  0;
}
foreach([341,1387,1729,13747,14491,15709],P,print(P," ",f(P,600)))
