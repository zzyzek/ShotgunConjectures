A(n)=sum(k=0,n,binomial(n,k)^2*binomial(n+k,k)^2);
bad=0;forprime(p=5,400,s=sum(k=0,p-1,A(k));m=p%8;if(m==5||m==7,if(s%p^2,bad++),q=qfbsolve(Qfb(1,0,2),p);x=q[1];if((s-(4*x^2-2*p))%p^2,bad++)));print("bad ",bad);
bad2=0;for(n=1,300,if(sum(k=0,n-1,(2*k+1)*A(k))%n,bad2++));print("intbad ",bad2);
