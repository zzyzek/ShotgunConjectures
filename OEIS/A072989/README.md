# OEIS A072989: the set has density one, so a(n)/n → 1 (the stated limit 0 is false)

**Source.** OEIS [A072989](https://oeis.org/A072989): numbers m > 0 such that the number of
solutions of x^m ≡ 1 (mod m), 1 ≤ x ≤ m, is not equal to gcd(m, φ(m)). Conjecture (OEIS wiki
conjecture list): "limit of a(n)/n is zero." Comment by M. F. Hasler (Feb 24 2014): this is
"certainly wrong as stated" (OEIS text, CC BY-SA 4.0).

**Reading.** Literally, a(n)/n → 0 is impossible for an increasing integer sequence once the
sequence is infinite, since a(n) ≥ n. The likely intended claim is that the set has density
zero (n/a(n) → 0). Both readings are false: the set has natural density 1, so a(n)/n → 1.

**Result.**
1. (Lean) If m ≡ 2 (mod 4) and m = A·B with gcd(A, B) = 1 and A, B > 2, then m is in A072989.
   In particular 6·5^j (j ≥ 1) is a term, the set is infinite, a(n) ≥ n, and a(n)/n does not tend to 0.
2. (Outside Lean) The set has natural density 1, so a(n)/n → 1.
Counts: 14 terms ≤ 100, 318 ≤ 10^3, 4081 ≤ 10^4, 45512 ≤ 10^5, 483517 ≤ 10^6,
5031230 ≤ 10^7 (density 0.503 at 10^7, rising slowly, as the log log m growth below predicts).

**Argument.** Write N(m) = #{x mod m : x^m ≡ 1}. The solutions are units and form the
kernel of u ↦ u^m on G = (ℤ/m)^×. By the Chinese remainder theorem G = ∏_{p^e ∥ m} G_p, so
N(m) = ∏_p N_p with N_p = #{g ∈ G_p : g^m = 1}; for odd p the group G_p is cyclic and
N_p = gcd(m, φ(p^e)).

*Lemma.* Let q be a prime with q | m, and let ω_q(m) be the number of primes p | m with
p ≡ 1 (mod q). If ω_q(m) > v_q(m) then m is a term.
Proof: each such p gives q | N_p, so q^{ω_q(m)} | N(m), while v_q(gcd(m, φ(m))) ≤ v_q(m).

For q = 2 this gives part 1: if v_2(m) = 1 and m has two odd prime factors then 4 | N(m)
and 4 ∤ gcd(m, φ(m)). (The Lean proof uses the splitting m = A·B and the element −1 of order 2
in each factor.)

*Density one.* For a fixed prime q, Σ_{p ≡ 1 (q)} 1/p diverges (Dirichlet). Take a finite set P of
such primes with Σ_{p∈P} 1/p = μ. The divisibility events {p | m}, p ∈ P, are independent in the
limit with probabilities 1/p, so the count of p ∈ P dividing m has mean μ and variance ≤ μ;
by Chebyshev the density of m with ω_q(m) < K is at most μ/(μ − K)², and letting μ → ∞ it is 0.
Now fix y and K. A non-term m falls in one of three classes: (a) no prime factor ≤ y, density
∏_{q ≤ y}(1 − 1/q); (b) some q ≤ y with v_q(m) ≥ K, density ≤ Σ_q q^{−K} ≤ 2^{1−K}; (c) some
q ≤ y with q | m and v_q(m) < K, and then (Lemma) ω_q(m) ≤ v_q(m) < K, density 0 for each of the
finitely many q. So the upper density of the complement is at most ∏_{q≤y}(1 − 1/q) + 2^{1−K},
which tends to 0 as y, K → ∞. Hence the terms have density 1 and a(n)/n → 1.

**Evidence.**
- Lean (Mathlib): [`A072989_mathlib.lean`](A072989_mathlib.lean). `A072989_two_mod_four`
  (part 1), `A072989_infinite`, `A072989_ge` (a(n) ≥ n), `A072989_main`
  (¬ a(n)/n → 0). The sequence is defined from the source text: count of 1 ≤ x ≤ m with
  x^m mod m = 1 mod m, compared with `Nat.gcd m (Nat.totient m)`, enumerated by `Nat.nth`.
  Axioms propext, Classical.choice, Quot.sound; zero warnings.
  Outside Lean: the density-one theorem (argument above; uses Dirichlet's theorem in the form
  Σ_{p≡1 (q)} 1/p = ∞ and a second-moment bound).
- `certificate/dens.py`: computes N(m) from the unit-group structure, checks it against brute
  force for m < 1500, reproduces the 54 listed terms and the counts above (`certificate/dens.out`).

**Review level.** `lean-proof` for the literal disproof and the m ≡ 2 (mod 4) family;
`rechecked` (paper proof) for density one.

**Prior art.** The OEIS entry (checked 2026-11-07) lists the conjecture and Hasler's comment
that it is wrong as stated; it gives no corrected statement or density. Web search 2026-11-07
(solution counts of x^m ≡ 1 mod m against gcd(m, φ(m))) found nothing further.
google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs: no entry for A072989
(local clones, 2026-11-07).
