E=ellinit([0,(3/2)^2+2,0,1,0]); print(elltors(E)); print(ellrank(E)[1..2]); print(ellanalyticrank(E)[1]);
for(i=1,4,P=[[2,2],[2,-1/2],[-1/2,2],[-1/2,-1/2]][i]; s=P[1]; t=P[2]; print((s+t)*(s*t-1)-3*s*t));
quit
