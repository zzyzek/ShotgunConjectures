# OEIS A005329: Product (2^i − 1) is the inverse binomial transform of A075272

**Source.** OEIS [A005329](https://oeis.org/A005329), a(n) = Product_{i=1..n} (2^i − 1). Comment
(J. W. Layman, Sep 2002): "Conjecture: this sequence is the inverse binomial transform of A075272 or,
equivalently, the inverse binomial transform of the BinomialMean transform of A075271." (OEIS text,
CC BY-SA 4.0; still a conjecture on 2026-11-06.) [A075271](https://oeis.org/A075271): a(0) = 1 and
(BM a)(n) = 2 a(n−1) for n ≥ 1, with (BM a)(n) = 2^(−n) Sum_{k=0..n} C(n,k) a(k).
[A075272](https://oeis.org/A075272) = BM(A075271).

**Result.** True.

**Argument.** Let c = A005329, so c(j+1) = (2^(j+1) − 1) c(j), and b(n) = Sum_k C(n,k) c(k). By Pascal's rule
b(k+1) = Sum_j C(k,j) (c(j) + c(j+1)) = Sum_j C(k,j) 2^(j+1) c(j). Applying the binomial transform twice,
Sum_k C(n,k) Sum_j C(k,j) d(j) = Sum_j C(n,j) 2^(n−j) d(j), so
Sum_k C(n,k) b(k+1) = Sum_j C(n,j) 2^(n−j) 2^(j+1) c(j) = 2^(n+1) b(n).
Hence a'(n) = b(n+1)/2 satisfies a'(0) = (c(0)+c(1))/2 = 1 and (BM a')(n+1) = b(n+1) = 2 a'(n). The
recurrence of A075271 determines each a(n+1) from a(0..n) (it enters with coefficient 1), so A075271 = a'
and A075272(n) = (BM a')(n) = b(n) for all n (n = 0: both are 1). So A075272 is the binomial transform
of A005329, and by binomial inversion A005329 is its inverse binomial transform. In egf terms the key
step is C(x) + C'(x) = 2 C(2x) for the egf C of c.

**Evidence.**
- Lean (Mathlib): [`A005329_mathlib.lean`](A005329_mathlib.lean), `A005329_main`: for every a : ℕ → ℚ with
  a 0 = 1 and BM a (n+1) = 2 a n, BM a n = Sum_k C(n,k) c(k) and c(n) = Sum_k (−1)^(n−k) C(n,k) BM a k for
  all n. `A005329_exists` shows the hypotheses are satisfiable, `A005329_unique` that they determine a.
  Lemmas: `A005329_pascal`, `A005329_twofold` (Sum_k C(n,k) x^(n−k) (T d)(k) = Sum_j C(n,j) (x+1)^(n−j) d(j),
  giving the double transform at x = 1 and binomial inversion at x = −1), `A005329_key`.
  Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py`: recomputes A075271 and A075272 from the definitions (40 terms), matches the OEIS
  data, and checks the identities.
- Outside Lean: that the Lean definitions transcribe the OEIS definitions (over ℚ).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: the A005329 entry still states the conjecture; A075272 has the
unproved comment "Binomial transform of A005329" (V. Reshetnikov, 2015), a g.f. (Jovovic 2008) and a
continued fraction (Bala 2017), no proof of the identity; A152476 (inverse binomial transform of
A005329) has none either. Web search found no proof; not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs (local clones, 2026-11-05 and 2026-10-13). The argument is a two-line
generating-function check, so it is new only as a written proof.
