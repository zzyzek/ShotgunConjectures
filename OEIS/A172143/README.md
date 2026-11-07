# OEIS A172143: the sequence is the union of the chains S(m, i)

**Source.** OEIS [A172143](https://oeis.org/A172143) (Ralf Stephan 2010). Original name
(A172126(n) − 1)/3, where [A172126](https://oeis.org/A172126) lists the numbers 2^l (4^j − 1)/3
(j ≥ 1) that are 1 mod 3. Comment (2010): "Conjecture: sequence consists of an infinite number of
subsequences … S(m, n) = [(3*A172241(m)+1)*4^n − 1]/3", A172241(m) = (8^m − (−1)^m − 9)/18. On
2025-12-18 Stephan replaced the name by explicit forms derived from the Collatz rules and dropped the
conjecture.

**Result.** True: a is a term iff 3a + 1 = (3·A172241(m) + 1)·4^i for some m ≥ 1, i ≥ 0.

**Argument.** (4^j − 1)/3 ≡ j and 2^l ≡ (−1)^l (mod 3), so 2^l (4^j − 1)/3 ≡ 1 forces (l even,
j ≡ 1) or (l odd, j ≡ 2) mod 3. With 64^k = 63q + 1: (4^{3k+1} − 1)/3 = 84q + 1 = 3·A172241(2k+1) + 1
and 2(4^{3k+2} − 1)/3 = 672q + 10 = 3·A172241(2k+2) + 1; the factor 4^{⌊l/2⌋} gives i.

**Evidence.** Lean (Mathlib): [`A172143_mathlib.lean`](A172143_mathlib.lean), `A172143_main`
(original definition ↔ conjecture, for every a), with `A172241_odd`, `A172241_even`. Axioms propext,
Classical.choice, Quot.sound. Outside Lean: reading A172126 as its comment's form
2^m(4^k − 1)/3 ≡ 1 (mod 3).

**Review level.** `lean-proof`.

**Prior art.** Known in substance: Stephan's 2025 name change (closed forms "derived from Collatz
rules", sketched only). Not in formal-conjectures or oeis-lean-proofs (2026-11-07).
