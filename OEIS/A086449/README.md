# OEIS A086449: parity of a(n) and a(2^k − 2)

**Source.** [A086449](https://oeis.org/A086449) (a(0) = 1, a(2n+1) = a(n), a(2n) = a(n) + a(n−1) + a(n−2) +
a(n−4) + …, a(<0) = 0), comment: "Conjecture: all a(n) are even except a(2^k-1) = 1. Also a(2^k-2) = 2^(k-1).
[For proof see link.]" (OEIS text, CC BY-SA 4.0.)

**Result.** True. Proof linked in the entry (L. Herrgesell); re-derived here.

**Argument.** a(2^k − 1) = a(2^(k−1) − 1) = … = a(0) = 1. Strong induction for evenness: an odd n = 2m+1
not of the form 2^k − 1 has m not of that form. For n = 2m (m ≥ 1), a(2m) = a(m) + Σ_j a(m − 2^j), and by
induction the odd terms are those with argument 2^i − 1: [m + 1 = 2^k] + #{j : m + 1 = 2^i + 2^j}. If
m + 1 = 2^k this is 1 + 1; if m + 1 has two 1-bits it is 0 + 2; otherwise 0. So a(2m) is even.
For a(2^k − 2), m = 2^(k−1) − 1: m − 2^j has j trailing ones, then the bits of 2^(k−1−j) − 2, so
a(m − 2^j) = a(2^(k−1−j) − 2) = 2^(k−j−2) for j ≤ k − 3 and a(0) = 1 for j = k − 2. Then
a(2^k − 2) = 1 + (2^(k−2) + … + 2) + 1 = 2^(k−1).

**Evidence.**
- `certificate/check.py`: n < 2^16.
- No Lean file.

**Review level.** `rechecked`.
**Prior art.** L. Herrgesell, proof file linked from A086449 (not read here; the argument above is independent).
Checked 2026-11-01. Resolved by others.
