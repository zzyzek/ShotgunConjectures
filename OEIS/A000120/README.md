# OEIS A000120: columns of the base-b digit-sum triangle are constant

**Source.** OEIS wiki Talk:Conjectures/List, entry for [A000120](https://oeis.org/A000120) (line 19):
"Conjecture: The sequence where a(n) is the sum of digits of (n written in base b), can be written as a
triangle T(r,k) in which all positive terms in column k are equal. Row 0 is a(0)=0 and row r lists
a(b^(r-1)) .. a(b^r - 1), for r>=1 and b>=2." (OEIS text, CC BY-SA 4.0.) The current entry shows the
b = 2 triangle (G. W. Adamson) but not this conjecture.

**Reading.** Column k (k ≥ 0) of row r ≥ 1 is s_b(b^(r−1) + k), present when k < (b−1)·b^(r−1).

**Result.** True; trivial. Every entry of column k equals 1 + s_b(k).

**Argument.** Write k = b^(r−1)·t + k' with k' < b^(r−1); then t < b − 1, so
b^(r−1) + k = b^(r−1)·(t+1) + k' with t + 1 a single digit. Digit sums split across a power of b:
s_b(b^j·t + k') = s_b(t) + s_b(k') for k' < b^j. Hence s_b(b^(r−1)+k) = (t+1) + s_b(k') = 1 + s_b(k).

**Evidence.**
- Lean: [`A000120.lean`](A000120.lean) defines s_b and proves `column`:
  s_b(b^j + k) = 1 + s_b(k) for all b ≥ 2, j, k < (b−1)·b^j. Axioms: propext, Quot.sound. Nothing outside Lean.
- `certificate/check.py`: b = 2..12, all rows with b^r ≤ 10^6.

**Review level.** `lean-proof`.
**Prior art.** No source found stating it; trivial (digit sums split across a power of b). The conjecture is not in the current [A000120](https://oeis.org/A000120). Checked 2026-11-04.
