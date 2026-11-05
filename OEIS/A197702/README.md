# OEIS A197702: least k with n = ±1 ±3 ± … ±(2k−1)

**Source.** [A197702](https://oeis.org/A197702) (offset 1), comment by J. W. Layman: "Conjecture. Let SO(k)
be the sum of the first k odd positive integers. Then a(n)=k if n=SO(k). Otherwise, choose k so that
SO(k-1)<n<SO(k). Then if SO(k)-n=4, a(n)=k+2, else if SO(k)-n is odd then a(n)=k+1 else a(n)=k." (OEIS
text, CC BY-SA 4.0; still stated on 2026-11-05, "verified for n up to 200".)

**Result.** True for every n ≥ 1. SO(k) = k².

**Argument.** Let S_k be the set of values ±1 ±3 … ±(2k−1). Claim: m ∈ S_k iff |m| ≤ k², k² − m is even
and |m| ≠ k² − 4 (equivalently, for k ≥ 2 the subset sums of {1, 3, …, 2k−1} are [0, k²] minus
{2, k² − 2}). Induction on k with S_{k+1} = (S_k + 2k+1) ∪ (S_k − 2k−1): the forward direction is direct;
backwards, for m ≥ 0 take m − (2k+1) unless it equals −(k² − 4), and then m + (2k+1) works (uses k² ≥ 4k
for k ≥ 4; k ≤ 3 by the exact values of k²; m < 0 is symmetric). Now let (k−1)² < n ≤ k². No j < k works
since n > j². If n = k², j = k works. If d = k² − n is odd, k fails by parity and k + 1 works. If d = 4,
k is excluded, k + 1 fails by parity, k + 2 works (d becomes 4k + 8). Otherwise d is even and ≠ 4, and k works.

**Evidence.**
- Lean (Mathlib): [`A197702_mathlib.lean`](A197702_mathlib.lean). `S k` is the finset of signed sums,
  `a n = sInf {k | 0 < k ∧ (n : ℤ) ∈ S k}`. Theorems: `mem_S` (the claim above);
  `A197702_square`: 1 ≤ k → a (k²) = k; `A197702_between`: (k−1)² < n < k² → a n = (if k² − n = 4 then k+2
  else if (k² − n) % 2 = 1 then k+1 else k); `A197702_conjecture`: 1 ≤ n → a n = rule n, with
  k = ⌊√(n−1)⌋ + 1 in `rule`; `rule_data` checks rule(1..40) against the data. Axioms: propext,
  Classical.choice, Quot.sound.
- `certificate/check.py`: the S_k characterization for k ≤ 60, rule = brute force for n ≤ 20000, rule = b-file
  (Heinz, n ≤ 10000; path given as argument, not stored here).
- Outside Lean: nothing.

**Review level.** `lean-proof`.

**Prior art.** New, immediate (checked 2026-11-05). Not in google-deepmind/formal-conjectures; no
A197702 file in otoi-lab/oeis-lean-proofs or epoch-research/LeanOpenProblems-results; web search found no
proof of the rule or of the subset-sum description.
