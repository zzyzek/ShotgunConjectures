# OEIS A166407: A166406(n)/(2n+1) is an integer except on A166101, where its denominator is 3

**Source.** [A166407](https://oeis.org/A166407) (offset 0): "a(n) = floor(3*(A166406(n)/A005408(n)))." Comment:
"Conjecture: the quotient A166406(i)/A005408(i) has denominator 3 when i is one of the terms of A166101, and it is
integral in other cases. If true, then floor in the formula is unnecessary." Here N = 2n+1 = A005408(n),
A166406(n) = Σ_{i≤N, J(i,N)=-1} i − Σ_{i≤N, J(i,N)=+1} i (J = Jacobi symbol), A166100(n) = Σ_{i≤N, J(i,N)=+1} i,
and A166101 lists the n with A166100(n)/N not an integer. (OEIS text, revision #14 of May 08 2021, checked
2026-11-06.)

**Result.** True. Write N = N'·m^2 with N' squarefree and B = −A166406(n)/N = (1/N) Σ_{i≤N} i·J(i,N). Then B is
an integer unless N' = 3 and every prime p ≠ 3 dividing m is ≡ 2 (mod 3); in that case B = −2^w/3 (w = number of
such primes) and n ∈ A166101. Whenever B is an integer, A166100(n)/N is an integer, so n ∉ A166101. Hence
A166101 = {n : 2n+1 = 3m^2, all prime factors p ≠ 3 of m are ≡ 2 (mod 3)} (= 1, 13, 37, 121, 181, ...).

**Argument.** χ(i) = J(i,N) is a real Dirichlet character mod N; on i coprime to N it equals the Jacobi symbol
mod N', the primitive real character of conductor N' (principal if N' = 1). B = (1/N) Σ_{a=1}^{N} a χ(a) is the
generalized Bernoulli number B_{1,χ} for nonprincipal χ.
1. *N' = 1* (N a square): B = (1/N) Σ_{(a,N)=1} a = φ(N)/2 for N > 1, and B = 1 for N = 1.
2. *χ even* (N' ≡ 1 mod 4, N' > 1): a ↦ N − a gives B = −B, so B = 0.
3. *χ odd* (N' ≡ 3 mod 4): B_{1,χ} = B_{1,χ_d} Π_{p | m, p ∤ N'} (1 − χ_d(p)) with d = −N' a fundamental
   discriminant (imprimitive characters: Washington, Cyclotomic Fields, Ch. 4), and B_{1,χ_d} = −2h(d)/w(d) (class
   number formula; w = 6 for d = −3, w = 2 for d < −4). So B ∈ ℤ unless d = −3, where B = −(1/3) Π (1 − χ_{−3}(p))
   ∈ {0, −2^w/3}; it is 0 as soon as some p ≡ 1 (mod 3) divides m.
4. *Link to A166100.* For N > 1, Σ_{(a,N)=1} a = Nφ(N)/2, so A166100(n)/N = φ(N)/4 + B/2. If B has denominator
   3, so does this. If B ∈ ℤ we need φ(N) + 2B ≡ 0 (mod 4): in case 1, B = φ(N)/2 and φ(N) + 2B = 2φ(N) ≡ 0
   (N > 2); in case 2, B = 0 and φ(N) ≡ 0 (mod 4) because N' has a prime ≡ 1 mod 4 or two primes; in case 3,
   if some p | m does not divide N' then B is even and φ(N) ≡ 0 (mod 4) (two distinct primes), and otherwise
   B = −h(−N'), which is odd when N' is prime (then N = p^k with k odd, φ(N) ≡ 2 mod 4) and even when N' has
   at least two prime factors (genus theory; then φ(N) ≡ 0 mod 4).

**Evidence.**
- [`certificate/check.py`](certificate/check.py) (run for n ≤ 6000): reproduces the b-files of A166406, A166100,
  A166407; every quotient has denominator 1 or 3; denominator 3 exactly on A166101; the predicted set and the
  value −2^w/3 hold.
- [`certificate/check_a166101.py`](certificate/check_a166101.py): the predicted set equals all 92 terms of the
  A166101 b-file (n ≤ 226981).
- Lean: none. Outside Lean: steps 1-4, which use B_{1,χ} for imprimitive characters, the analytic class number
  formula and Gauss's genus theory (parity of h(−N')); none of these is in Mathlib in usable form.

**Review level.** `rechecked`.

**Prior art** (2026-11-06). OEIS A166407, A166406, A166408 (conjecture repeated), A166101, A166102, A166272 (related
conjectures, no proof); google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs: no file. The identity
Σ a χ(a) = N·B_{1,χ} and the class number formula are classical; their application here is ours.
