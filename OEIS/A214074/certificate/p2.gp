{forprime(q=5,3*10^6,
  my(d2=znorder(Mod(2,q)), d3=znorder(Mod(3,q)));
  if(d3%d2==0, my(t=znlog(Mod(2,q),Mod(3,q),d3)); if(t%d2==1%d2, print("P2 ",q," mod ",d3," res ",t)));
  if(d2%d3==0, my(s=znlog(Mod(3,q),Mod(2,q),d2)); if(s%d3==1%d3,
     print("P3 ",q," mod ",d2," res ",s," compat121 ",(s-121)%gcd(d2,330)==0))));}
quit
