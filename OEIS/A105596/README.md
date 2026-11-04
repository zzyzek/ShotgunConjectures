# OEIS A105596: the self-convolution with alternating signs is 1 mod 4

**Source.** [A105596](https://oeis.org/A105596) (a(n) = Σ_k A105595(k)(−1)^k A105595(n−k), interpolated zeros
suppressed), comment: "Conjecture : a(2n)=1 mod 4 for all n, a(2n+1)=0 for all n." (OEIS text, CC BY-SA 4.0.)

**Reading.** The indices refer to the unsuppressed convolution c(m) = Σ_{k≤m} (−1)^k b(k) b(m−k), b = A105595;
the printed sequence is c(2n).

**Result.** True, given that every A105595 term is odd (proved in A105595 by B. Gao, Sep 2026).

**Argument.** For odd m the terms k and m − k carry opposite signs and cancel, so c(m) = 0. For m = 2n,
c(2n) = 2Σ_{k<n} (−1)^k b(k) b(2n−k) + (−1)^n b(n)². Each b is odd, so each term of the sum is ±2 (mod 4) and the
sum contributes 2n (mod 4); b(n)² ≡ 1 (mod 8). Hence c(2n) ≡ 2n + (−1)^n ≡ 1 (mod 4).

**Evidence.**
- `certificate/check.py`: A105594/A105595 from the definition (|μ| of binomials via squarefreeness), b odd,
  c(odd) = 0 and c(even) ≡ 1 (mod 4) for m < 120, and agreement with the A105596 data.
- Lean (Mathlib): [`A105596_mathlib.lean`](A105596_mathlib.lean), `A105596_main`: for every b : ℕ → ℤ with all values odd, c(2n+1) = 0 and c(2n) ≡ 1 (mod 4) for c(m) = Σ_k (-1)^k b(k) b(m-k). Outside Lean: that all A105595 terms are odd (B. Gao).

**Review level.** `lean-witness`: the mod-4 argument is proved in Lean for every odd sequence; the oddness of A105595 (Gao) is outside Lean.
**Prior art.** Verdict new, immediate (OEIS status conjecture; searched 2026-11-04). The oddness input is Gao's; the mod-4 step from it to A105596 is stated nowhere. Sources: [OEIS A105596 (fetched 2026-11-04)](https://oeis.org/A105596): still says Conjecture; no proof, no 2026 edits; [Bing Gao, comment in OEIS A105595 (Sep 2026)](https://oeis.org/A105595): proves all A105595 terms odd (the input lemma). Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; OEIS A105595, A105597; Google: A105596.
