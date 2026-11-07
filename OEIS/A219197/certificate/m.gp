default(parisizemax, 1500000000);
N=1200;
G=sum(n=0,N,binomial(3*n,n)/(2*n+1)*x^n)+O(x^(N+1));
A=G/sqrt(1-2*x*G^2-3*x^2*G^4);
v=vector(N+1,n,polcoeff(A,n-1)%4);
print(v[1..96]);
for(r=0,3, print(r, ": ", #select(t->t==r, v)));
print("odd positions n: ", select(n->v[n+1]%2==1, [0..200]));
