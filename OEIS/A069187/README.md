# OEIS A069187: core(k) = ⌈√k⌉ exactly for k = 1 and k = n²(n²+1) with n²+1 squarefree

**Source.** [A069187](https://oeis.org/A069187), numbers k with core(k) = ⌈√k⌉ (core = squarefree part).
Comment by R. Stephan (Aug 18 2004): "Conjecture: sequence is A071253 minus those entries of A071253 that have
their index in A049532, i.e., a(n) is of form n^2*(n^2+1) for all n not in A049532." (OEIS text, CC BY-SA 4.0,
read 2026-11-06.) A071253(n) = n²(n²+1) (offset 0); A049532 = n with n²+1 not squarefree.

**Result.** True, with one correction at the start: the terms are 1 and the n²(n²+1) with n ≥ 1 and n²+1
squarefree. A071253(0) = 0 is not a term and 1 is not in A071253.

**Argument.** Write k = b²a with a squarefree; then core(k) = a. ⌈√k⌉ = a means (a−1)² < b²a ≤ a². The right
inequality gives b² ≤ a. If a ≥ b² + 2 then b²a ≤ (a−2)a < (a−1)², a contradiction. So a = b² (squarefree forces
b = 1, k = 1) or a = b² + 1 (k = b²(b²+1) with b²+1 squarefree). Conversely both kinds satisfy the inequalities.

**Evidence.**
- Lean (Mathlib): [`A069187_mathlib.lean`](A069187_mathlib.lean), `A069187.A069187_main`: for k ≥ 1,
  core k = ⌈√k⌉₊ ↔ k = 1 ∨ ∃ n ≥ 1, Squarefree (n²+1) ∧ k = n²(n²+1), with `core k` the least s ≥ 1 making k·s a
  square (the OEIS definition) and the real square root. Check `tools/leancheck-mathlib.sh`: OK, no warnings,
  axioms propext, Classical.choice, Quot.sound.
- Outside Lean: nothing beyond reading the definition.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: entry still says "Conjecture"; not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs (local clones). The argument is elementary; no published proof found.
