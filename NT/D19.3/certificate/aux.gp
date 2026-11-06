\\ auxiliary curve w^2 = (1-3s^2)(1+s^2), point (0,1)
c=ellfromeqn(w^2-(1-3*s^2)*(1+s^2)); E=ellinit(c); E=ellminimalmodel(E);
print("aux: ", E[1..5], " cond ", ellglobalred(E)[1], " tors ", elltors(E), " rank ", ellrank(E)[1..2], " an.rank ", ellanalyticrank(E)[1]);
\\ Evans curve torsion check directly
ev(r)=ellminimalmodel(ellinit([0,r^2+2,0,1,0]));
for(k=1,12, r=(k^2-4)/(2*k); if(r>0, E2=ev(r); print([r, elltors(E2)[2], ellrank(E2)[1..2]])));
quit
