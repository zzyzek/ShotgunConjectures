# OEIS A051924: a(n) ≡ n + 2 (mod n^2) also holds at n = 16843^2

**Source.** [A051924](https://oeis.org/A051924) (a(n) = C(2n,n) − C(2n−2,n−1) = (3n−2)·Catalan(n−1)),
comment by G. Detlefs (2013): "Conjecture: a(n) mod n^2 = n+2 iff n is an odd prime." (OEIS text, CC BY-SA 4.0.)

**Result.** False: n = 16843^2 = 283686649 is composite and a(n) ≡ n + 2 (mod n^2). The "if" direction
holds (Wolstenholme for p ≥ 5; a(3) = 14 ≡ 5).

**Argument.** a(n)(2n − 1) = C(2n−1, n−1)(3n − 2) and (n + 2)(2n − 1) = 2n^2 + 3n − 2 ≡ 3n − 2 (mod n^2);
2n − 1 is invertible mod n^2, so a(n) ≡ n + 2 (mod n^2) iff C(2n−1, n−1) ≡ 1 (mod n^2). Take n = p^2,
p an odd prime. In C(2n−1, n−1) = ∏_{k=1}^{n−1} (n+k)/k, the factors with p ∤ k multiply to
1 + n·Σ 1/k (mod p^4), and Σ_{k<p^2, p∤k} 1/k ≡ 0 (mod p^2) by pairing k with p^2 − k; the factors with
k = pj give ∏_{j<p} (p + j)/j = C(2p−1, p−1). So the condition at n = p^2 is C(2p−1, p−1) ≡ 1 (mod p^4):
p a Wolstenholme prime. 16843 is one (McIntosh 1995).

**Evidence.**
- Lean (Mathlib): [`A051924_mathlib.lean`](A051924_mathlib.lean) proves `A051924_main`: a(p) % p² = p + 2 for every odd prime p (Babbage's congruence C(2p-1, p-1) ≡ 1 mod p², by pairing k with p - k), and 283686649 = 16843² is odd, not prime, with a(283686649) % 283686649² = 283686649 + 2; `A051924_false`: the conjecture fails. The p-adic reduction is proved (a(n)(2n-1) = C(2n-1, n-1)(3n-2); C(2n-1, n-1)·(n-1)! = ∏(n+k); pairing on p ∤ k, the k = pj factors give p^(p-1)·∏(p+j)), with the kernel computation ∏_{j<p}(p+j) ≡ ∏_{j<p} j (mod p⁴) by a proved-correct binary-splitting product. Outside Lean: nothing.
- Lean: [`A051924.lean`](A051924.lean) (`decide +kernel`, binary-splitting product mod p^4):
  ∏_{j=1}^{p−1}(p + j) ≡ ∏_{j=1}^{p−1} j (mod p^4) for p = 16843, i.e. C(2p−1, p−1) ≡ 1 (mod p^4); and
  283686649 = 16843^2. Axioms: propext. Outside Lean: the p-adic reduction above.
- `certificate/a051924_wolst.c` (the scan's program, rerun 2026-11-01, 27 s): computes a(16843^2) mod 16843^4
  directly and gets 283686651 = n + 2. This is independent of the reduction.

**Review level.** `lean-proof`: proved in Lean + Mathlib ([`A051924_mathlib.lean`](A051924_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file and the C program remain as independent checks.
**Prior art.** Partly known. McIntosh ([Acta Arith. 71, 1995](https://eudml.org/doc/206780)) shows n = 16843^2 satisfies C(2n-1, n-1) == 1 (mod n^2); the equivalence with Detlefs' congruence is two lines and is not stated anywhere found. [A051924](https://oeis.org/A051924) still has the conjecture. Searched OEIS entry, references and history, web. Checked 2026-11-04.
