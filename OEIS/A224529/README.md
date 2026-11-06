# OEIS A224529: a(np) ≡ a(n) mod p for (p/23) = 1 (proved by Osburn and Sahu)

**Source.** OEIS [A224529](https://oeis.org/A224529) (f_n of Osburn and Sahu), comment by
Michael Somos (Sep 21 2013): "Conjecture 1.1 of Osburn and Sahu is if p is a prime and
JacobiSymbol(p, 23) = 1 and n>0 then a(n * p) == a(n) (mod p)."

**Reading.** f(z) = Σ_{m,n} q^{m²+mn+6n²}, t = η(z)η(23z)/f(z), and a(n) = f_n is the
coefficient of tⁿ in f written as a power series in t (the entry's definition).

**Result.** True; proved. Conjecture 1.1 in the cited paper is the conjecture of Chan, Cooper
and Sica, and the paper proves it: Theorem 1.2 of R. Osburn, B. Sahu, *Congruences via
modular forms*, Proc. AMS 139 (2011) 2375–2381 (arXiv:0912.0173) gives
f_{np^r} ≡ f_{np^{r−1}} (mod p^r) for all n, r ≥ 1 and primes p with (p/23) = 1; r = 1 is the
claim. The comment's wording ("conjecture") is out of date, not a different claim.

**Argument.** (Osburn–Sahu, not re-derived.) f and t relate to the weight-3 Eisenstein space
E₃(Γ₀(23), (·/23)); the congruences follow from the coefficient congruences of those
Eisenstein series by the Beukers-type argument for power series in a modular function.

**Evidence.** `certificate/a224529.py`: computes a(n), n ≤ 1000, from Somos' recurrence,
matches the b-file (n ≤ 1000), and checks a(np) ≡ a(n) mod p for all 1196 pairs with
np ≤ 1000 and (p/23) = 1 (p = 2, 3, 13, 29, …). No Lean: the proof needs modular forms.

**Review level.** `agent` (citation read in the paper's statement; numerics rechecked).

**Prior art.** Checked 2026-11-06: OEIS entry; arXiv:0912.0173 (Theorem 1.2);
google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs (no entry).
