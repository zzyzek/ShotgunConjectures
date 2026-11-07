# OEIS A220956: "a(n) = 0 iff n is an odd prime" is false; n = 16843² = 283686649 is a composite zero

**Source.** [A220956](https://oeis.org/A220956), a(n) = (C(2n,n) − C(2n−2,n−1)) mod n² − n − 2. Comment:
"Conjecture: a(n) = 0 iff n is an odd prime." (OEIS text, CC BY-SA 4.0, read 2026-11-06; b-file to n = 10100.)

**Result.** False. For odd n ≥ 3, a(n) = 0 exactly when C(2n−1,n−1) ≡ 1 (mod n²). Composite n with this
congruence are known ([A267824](https://oeis.org/A267824): 283686649 = 16843², 4514260853041 = 2124679², squares of
the Wolstenholme primes; McIntosh, "On the converse of Wolstenholme's theorem", Acta Arith. 71 (1995)). So
a(283686649) = 0 with 283686649 composite. The "if" direction holds for every odd prime (Babbage/Wolstenholme for
p ≥ 5, and a(3) = 0 directly).

**Argument.** Put B = C(2n−1,n−1), c = C(2n−2,n−1). Then C(2n,n) = 2B and nB = (2n−1)c, so with
D = C(2n,n) − c: (2n−1)(D − (n+2)) = (3n−2)(B − 1) − 2n². Since 0 < n + 2 < n², a(n) = 0 iff n² | D − (n+2).
2n − 1 is prime to n, and 3n − 2 is prime to n for odd n, so a(n) = 0 iff n² | B − 1.

**Evidence.**
- Lean (Mathlib): [`A220956_mathlib.lean`](A220956_mathlib.lean). `A220956_reduce` (odd n ≥ 3:
  a n = 0 ↔ n² ∣ C(2n−1,n−1) − 1, all n) and `A220956_counterexample` (283686649 = 16843·16843 is odd and not
  prime, and the congruence implies a = 0). Check `tools/leancheck-mathlib.sh`: OK, no warnings, axioms propext,
  Classical.choice, Quot.sound.
- [`certificate/binom_mod.c`](certificate/binom_mod.c): direct computation for n = 16843² (p-adic unit products
  mod n² = 16843⁴, 128-bit): C(2n−1,n−1) mod n² = 1, (C(2n,n) − C(2n−2,n−1)) mod n² = n + 2, a(n) = 0.
- Outside Lean: the single congruence C(2n−1,n−1) ≡ 1 (mod n²) for n = 16843² (this computation and McIntosh 1995).

**Review level.** `lean-proof` for the reduction; the congruence `rechecked` (independent computation + literature).

**Prior art.** Checked 2026-11-06: the entry still states the conjecture; the composite solutions of
C(2n−1,n−1) ≡ 1 (mod n²) are in A267824 and in McIntosh (1995) and the Wolstenholme survey
(Meštrović, arXiv:1111.3057). The link to A220956 was not stated there. Not in google-deepmind/formal-conjectures
or otoi-lab/oeis-lean-proofs (local clones).
