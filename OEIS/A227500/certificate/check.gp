\\ OEIS A227500: data terms from the definition, and (b-a)/c = fib(n-2) for n <= 300.
\\ bernfrac(1) = -1/2 (A027641/A027642); second Bernoulli numbers differ only at n = 1.
B1(n) = bernfrac(n);
B2(n) = if(n == 1, 1/2, bernfrac(n));
N = 300; r1 = vector(N+1); r2 = vector(N+1);
for(n = 2, N, r1[n+1] = r1[n] + r1[n-1] + B1(n-2); r2[n+1] = r2[n] + r2[n-1] + B2(n-2));
data = [0,0,1,1,5,13,19,179,1028,1103,893,2889,15445,249787,24988,8494711,6888613,7423979,101535859,329279361,1187585188,128951009,2513033741,25007430139,599126628077,591141383117,-3361274604,1470023540617,22712552603063,322385807064733,-26340115994784101];
ok = 1;
for(n = 0, #data-1, if(numerator(r1[n+1]) != data[n+1], ok = 0; print("data mismatch ", n)));
for(n = 0, N, if(denominator(r1[n+1]) != denominator(r2[n+1]), ok = 0; print("den mismatch ", n)); if((numerator(r2[n+1]) - numerator(r1[n+1]))/denominator(r1[n+1]) != if(n >= 2, fibonacci(n-2), 0), ok = 0; print("fib mismatch ", n)));
print(if(ok, "all checks passed, n <= 300", "FAILED"));
