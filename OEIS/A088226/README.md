# OEIS A088226: a(n) = |a(n-1) − a(n-2) − a(n-3)| is half the smallest even distance from n − 1 to a square

**Source.** OEIS [A088226](https://oeis.org/A088226) (offset 1): a(1) = 0, a(2) = 0, a(3) = 1,
a(n) = |a(n−1) − a(n−2) − a(n−3)| for n > 3: 0, 0, 1, 1, 0, 2, 1, 1, 2, 0, 3, ... Conjecture
(R. Stephan, Sep 2013): "a(n) = m/2 where m is the smallest even distance from n to a square."
(OEIS text, CC BY-SA 4.0; still a conjecture on 2026-11-05, revision #30.)

**Reading.** Let f(m) = (smallest even |m − s²|, s ≥ 0)/2. As printed (a(n) = f(n)) the conjecture is
false: a(2) = 0 but f(2) = 1 (2 is at distance 2 from 0 and from 4, distance 1 from 1). It also fails at
n = 4, 5, 6, 8, ... Stephan's PARI program in the entry computes f(n), and it does not reproduce the
data either (it gives 1 at n = 2 and 0 at n = 4). The entry's own formula a(k² + 2m + 1) = m,
a(k² + 2m + 2) = k − m (0 ≤ m ≤ k) is the shifted statement a(n) = f(n − 1).

**Result.** Corrected form true: a(n) = f(n − 1) for every n ≥ 1. The printed form is a misstatement by
one index.

**Argument.** Block formula: for k ≥ 0 and 1 ≤ j ≤ 2k + 1, a(k² + j) = (j − 1)/2 if j is odd and
k − (j − 2)/2 if j is even. Induction on k (k = 0, 1 by direct computation). Inside block k ≥ 2:
for j ≥ 4 the three previous terms are in the same block, and for odd j = 2m + 1
|(k − m + 1) − (m − 1) − (k − m + 2)| = m, for even j = 2m + 2 |m − (k − m + 1) − (m − 1)| = k − m.
For j = 1, 2, 3 the previous block ends with a(k²−2), a(k²−1), a(k²) = k − 2, 1, k − 1, giving
|k − 1 − 1 − (k − 2)| = 0, |0 − (k − 1) − 1| = k, |k − 0 − (k − 1)| = 1.
Distance side: n − 1 = k² + j − 1 is at distance j − 1 from k² and 2k + 2 − j from (k + 1)²; these
sum to 2k + 1, so exactly one is even, and it is (j − 1) for odd j and 2k + 2 − j for even j, i.e.
twice the block value. Squares s² with s ≤ k − 1 or s ≥ k + 2 are at distance ≥ 2k + j − 2 resp.
≥ 4k + 5 − j, never below the even candidate (which is ≤ 2k, and 0 when j = 1). Every n ≥ 1 is
k² + j with k = ⌊√(n−1)⌋ and 1 ≤ j ≤ 2k + 1.

**Evidence.**
- Lean (Mathlib): [`A088226_mathlib.lean`](A088226_mathlib.lean). `A088226_main (n) (hn : 1 ≤ n)`:
  `A088226_a n = A088226_f (n - 1)`, with `A088226_a` the recurrence and `A088226_f m` = (Nat.find of the
  least even d with d = |m − s²| for some s ∈ ℕ)/2. `A088226_literal_fails`: a(2) = 0 and f(2) = 1.
  `A088226_block`, `A088226_f_block` (the two halves of the argument), `A088226_data` (105 printed terms,
  `decide`). Axioms: propext, Classical.choice, Quot.sound.
- `certificate/check.py`: the 105 printed terms, a(n) = f(n − 1) for n ≤ 300000 (f by scanning all
  squares), the literal form failing at n = 2, 4, 5, 6, 8, ..., and the block formula.
- Outside Lean: nothing.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05: the entry lists the block formula (unattributed, without proof) next to
the conjecture; the shifted conjecture is equivalent to it given the distance computation above. A web
search found no proof; not in google-deepmind/formal-conjectures. The index slip in the printed
conjecture and in the PARI program is not noted in the entry.
