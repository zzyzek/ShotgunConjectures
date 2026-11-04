\\ A137328: every prime q appears as prime(n) - primorial(k) with k maximal,
\\ i.e. some primorial P#_k with p_k < q (else q | P#_k + q) has P#_k + q prime.
\\ Also P#_k must be the largest primorial <= P#_k + q, i.e. q < P#_k*(p_{k+1}-1).
\\ Report primes q < N needing the largest k, and any q with no such k.
{
N = 1000000; worst = 0; bad = [];
forprime(q = 3, N,
  P = 1; k = 0; found = 0; p = 1;
  while (1,
    if ((P * (nextprime(p + 1) - 1) > q) && ispseudoprime(P + q), found = 1; break);
    p = nextprime(p + 1);
    if (p >= q, break);
    P *= p; k++);
  if (!found, bad = concat(bad, q),
    if (k > worst, worst = k; print("q=", q, " needs k=", k))));
print("primes q < ", N, " with no valid k: ", bad);
}
