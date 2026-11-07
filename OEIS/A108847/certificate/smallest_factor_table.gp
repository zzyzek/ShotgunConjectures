for(d=4,5, v=vector(36,k, N=9*10^(k+1)+d*(10^k-1)/9*10+9; forprime(p=2,10^5, if(N%p==0, return_p=p; break)); return_p); print("d=",d," ",v))
