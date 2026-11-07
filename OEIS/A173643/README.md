# OEIS A173643: the odd-part formula needs K = 0 (counterexample 3)

**Source.** [A173643](https://oeis.org/A173643) (offset 1): "Positive numbers of form 2^m - 2^l - 3*2^k (A172233)
divisible by 9, divided by 9", with A172233 requiring m > l > k ≥ 0. Comment: "Conjecture: Odd part of a(n) is of
form [(1/6)*(8^m-(-1)^m-3)*4^k-1]/3, k,m>0." (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** The terms are (2^m − 2^l − 3·2^k)/9 with m > l > k ≥ 0, value positive and divisible by 9 (this
reproduces the 55 listed terms, certificate/check.py). Write F(M,K) = ((8^M − (−1)^M − 3)/6 · 4^K − 1)/3.

**Result.** As stated (K, M > 0) the conjecture is false: a(3) = 3 = (2^5 − 2^1 − 3)/9 has odd part 3, and
F(M,K) ≠ 3 for K, M > 0 (F(2,0) = 3). With K ≥ 0 allowed it is true. The odd parts missed by K > 0 are exactly
F(M,0) for even M: 3, 227, 14563, 932067, …, each of which is a term.

**Argument.** Put B = l − k ≥ 1, D = m − l ≥ 1. The term is 2^k·w with w = (2^B(2^D − 1) − 3)/9 odd, so w is the
odd part. Since 2^6 ≡ 1 (mod 9), 9 | 2^B(2^D − 1) − 3 iff (D ≡ 2 mod 6, B even) or (D ≡ 4 mod 6, B odd).
In the first case M = (D+1)/3 is odd, K = B/2 ≥ 1 and w = F(M,K); in the second M = (D+2)/3 is even,
K = (B−1)/2 ≥ 0 and w = F(M,K). F(M,0) for odd M is even, so it is never an odd part.

**Evidence.**
- Lean (Mathlib): [`A173643_mathlib.lean`](A173643_mathlib.lean). Main theorem `A173643_conjecture_false` (stated
  about `A173643_mem`, the OEIS definition, and the odd part a / 2^v_2(a)); `A173643_corrected` (every term's odd
  part is F(M,K) with M > 0, K ≥ 0). Check OK, no warnings; axioms propext, Classical.choice, Quot.sound.
- certificate/check.py: data match; odd parts below 10^15 compared with F for K ≥ 1 and K ≥ 0.
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: entry still states the conjecture with k, m > 0; not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
