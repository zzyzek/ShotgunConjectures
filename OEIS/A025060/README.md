# OEIS A025060: with signs allowed, i·j + j·k + k·i takes every integer

**Source.** [A025060](https://oeis.org/A025060), comment by J. Perry (2013): "Conjecture: If i, j and k are
allowed to be negative, but not zero, and are still distinct, then the sequence is all the integers."
(OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial.

**Argument.** (i, j) = (2, −1) gives ij + k(i + j) = k − 2, valid for k ∉ {0, 2, −1}: every integer
except −2, 0, −3. (i, j) = (4, −3) gives k − 12, valid for k ∉ {0, 4, −3}: covers −3 (k = 9), −2 (k = 10),
0 (k = 12). (The scan's note used (3, −2) as the second family, which misses −3 = k − 6 at the excluded
k = 3; the conclusion is unaffected. −3 has other representations, e.g. (4, −3, 9) above.)

**Evidence.**
- Lean: [`A025060.lean`](A025060.lean) proves `∀ v : Int, Rep v` with these triples. Axioms: propext,
  Quot.sound. Nothing outside Lean.

**Review level.** `lean-proof`.
**Prior art.** No source found; trivial (two explicit families). [A025060](https://oeis.org/A025060) still has the conjecture. Searched OEIS entry, references and history. Checked 2026-11-04.
