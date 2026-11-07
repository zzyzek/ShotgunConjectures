{forprime(q=5,3000, my(d2=znorder(Mod(2,q)), d3=znorder(Mod(3,q)), L=lcm(d2,d3), S=[]);
  for(r=0,L-1, if(Mod(2,q)^(r-1)==1 && Mod(3,q)^r==2, S=concat(S,r)));
  if(#S, print("P2 q=",q," d2=",d2," d3=",d3," L=",L," res=",S)));}
{forprime(p=5,3000, my(L=lcm(znorder(Mod(2,p)),znorder(Mod(3,p)))); if(L<=400, print("P1 p=",p," L=",L)));}
quit
