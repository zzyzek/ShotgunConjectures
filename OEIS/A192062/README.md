# OEIS A192062: the prime chain T(2n) = A(n)T(n), A(3n) = A(n)B(n), B(5n) = B(n)C(n), ... has integer factors

**Source.** [A192062](https://oeis.org/A192062) (Kenneth J. Ramsey, 2011), comment: "Conjecture re relation of
A192062 to the sequence of primes: T(2*n,j) = A(n,j)*T(n,j) where A(n,j) is from the square array A191971. There,
A(3*n,j) = A(n,j)*B(n,j) where B(n,j) are integers. ... My conjecture is that this property continues indefinitely
and follows the sequence of primes." (OEIS text, CC BY-SA 4.0, revision #23 of Dec 10 2016, checked 2026-11-06.)

**Reading.** Column j >= 0 of T is T(0)=0, T(1)=1, T(2i)=T(2i-2)+T(2i-1), T(2i+1)=T(2i-1)+j T(2i) (formula in the
entry). Column j of A191971 is A(0)=2, A(1)=1, A(2i)=j A(2i-1)+A(2i-2), A(2i+1)=A(2i)+A(2i-1). Let p_1, p_2, ... =
2, 3, 5, ... Put G_1 = T, G_2 = A and G_{k+1}(n) = G_k(p_k n)/G_k(n) (so G_3 = B, G_4 = C, ...). The conjecture:
for every k, j >= 0 and n >= 1, G_k(p_k n) = G_k(n) G_{k+1}(n) with G_{k+1}(n) an integer (and G_2 = A).

**Result.** True for every k, j and n >= 1. Every G_k(n) is a product of distinct "cyclotomic parts" of a Lehmer
sequence, and each G_{k+1}(n) is again such a product.

**Argument.**
1. *Lehmer form.* For j >= 1 let a, b be real with ab = -1 and a^2 + b^2 = j+2, so (a+b)^2 = j and a^2, b^2 are the
   two roots of x^2 - (j+2)x + 1. The Lehmer sequence L(n) = (a^n - b^n)/(a - b) (n odd), (a^n - b^n)/(a^2 - b^2)
   (n even) has L(0)=0, L(1)=1, L(2)=1, L(3)=a^2+ab+b^2=j+1 and L(n+4)=(j+2)L(n+2)-L(n). T satisfies the same
   recurrence (eliminate the odd terms from the two-step rule; it is the formula T(n+2) = (j+2)T(n) - T(n-2) in the
   entry) with the same four initial values, so T(n,j) = L(n). Likewise the companion V(n) = a^n + b^n (n even),
   (a^n + b^n)/(a + b) (n odd) has V(0)=2, V(1)=1, V(2)=j+2, V(3)=j+3 and the same order-4 recurrence, as does A;
   so A(n,j) = V(n).
2. *Cyclotomic parts.* Let P_d = b^{phi(d)} Phi_d(a/b), the homogenised cyclotomic polynomial. Then
   a^n - b^n = prod_{d | n} P_d, with P_1 = a - b and P_2 = a + b. Hence L(n) = prod_{d | n, d >= 3} P_d for every
   n >= 1. For d >= 3, Phi_d is self-reciprocal of even degree, so P_d is a symmetric form of even degree in a, b
   with integer coefficients, i.e. an integer polynomial in (a+b)^2 = j and ab = -1: P_d is an integer. a/b = -a^2
   has absolute value != 1, so P_d != 0.
3. *Exponent bookkeeping.* Write G_k(n) = prod_{d >= 3} P_d^{e_k(n,d)}. For G_1, e_1(n,d) = prod_q [v_q(d) <= v_q(n)]
   over all primes q. Claim: e_k(n,d) = prod_{i<k} [v_{p_i}(d) = v_{p_i}(n)+1] * prod_{q not in {p_1..p_{k-1}}}
   [v_q(d) <= v_q(n)], which is 0 or 1. Induction: replacing n by p_k n changes only the factor for q = p_k, from
   [v <= v_{p_k}(n)] to [v <= v_{p_k}(n)+1]; the difference is [v = v_{p_k}(n)+1] >= 0, so G_k(p_k n)/G_k(n) =
   prod P_d^{e_{k+1}(n,d)} with e_{k+1} of the claimed form. Since the P_d (d >= 3) are nonzero integers, every
   G_k(n) is an integer and G_k(p_k n) = G_k(n) G_{k+1}(n). For k = 1 this gives T(2n)/T(n) = prod_{d | 2n, d not
   dividing n, d >= 3} P_d = V(n) = A(n) (for n odd the factor P_2 = a+b is excluded, giving (a^n+b^n)/(a+b)).
4. *j = 0.* Here T(2i)=i, T(2i+1)=1, A(n)=n for odd n and 2 for even n, so B(n) = A(3n)/A(n) = 3 (n odd), 1 (n
   even), and C = B(5n)/B(n) = 1, after which every G_k is 1.

**Evidence.**
- [`certificate/chain.py`](certificate/chain.py): for j = 0..12 checks T(2n) = A(n)T(n) and the integrality of
  G_2..G_6 (primes 2, 3, 5, 7, 11) for n up to 12 * 2310 / (product of the primes already used); 0 failures, exit 0
  (55 s).
- Lean (Mathlib): [`A192062_mathlib.lean`](A192062_mathlib.lean). `Gchain j 0 = T`, `Gchain j (k+1) n =
  Gchain j k (p_k n) / Gchain j k n` with p_k = `Nat.nth Nat.Prime k` (so `Gchain j k` is G_(k+1) above).
  `A192062_main`: for all j, k and n >= 1, Gchain j k n >= 1 divides Gchain j k (p_k n) and
  Gchain j k (p_k n) = Gchain j k n * Gchain j (k+1) n. `A192062_G1`: Gchain j 1 n = A(n, j) (n >= 1), from
  `T_double`: T(2n) = A(n) T(n). The Lean proof does not use cyclotomic polynomials: T is a strong divisibility
  sequence (`T_gcd`, via the addition formula T(m+n+1) = c1 T(m+1) T(n+1) + c2 T(m) T(n), c1 = j for m, n odd,
  c2 = j for m, n even, else 1), so v_l(T(gcd(a,b))) = min(v_l T(a), v_l T(b)) for every prime l; the k-th iterated
  quotient has v_l equal to the k-th iterated difference of v_l o T, which is >= 0 for every gcd-to-min function
  (`gd_nonneg`; induction on k with f(nd) = min(f(p_k n d), f(n p_0...p_(k-1))) and max(f - c, 0)).
  Axioms: propext, Classical.choice, Quot.sound.
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry and A191971 state the chain only as a conjecture. The ingredients
(Lehmer sequences and their cyclotomic factorisation, D. H. Lehmer, Ann. Math. 31 (1930)) are classical; we found no
write-up of this chain. Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
