doit(r)={my(c,E,T,R);
  c=ellfromeqn((x+y)*(x*y-1)-2*r*x*y);
  E=ellinit(c); if(E==[], return([r,"sing"]));
  E=ellminimalmodel(E);
  T=elltors(E)[1];
  R=ellrank(E);
  [r, T, elltors(E)[2], R[1], R[2]]};
for(n=1,40, print(doit(n)); print(doit(1/n)));
print(doit(4/3)); print(doit(42));
quit
