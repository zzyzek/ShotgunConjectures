# Coman P115: Carmichael numbers divisible by 37 and 73 (C173, C174)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 115. Paraphrase: Study conjectures 173 and 174.

**Result.** Both false (see C173/C174: 294409).

**Argument and evidence.** This item restates [COM-C173](../C173/README.md), [COM-C174](../C174/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C173/C173.lean`](../C173/C173.lean).
Lean (Mathlib): [`C173_mathlib.lean`](../C173/C173_mathlib.lean) (`C173_false`) proves the result in full; outside Lean: none.

**Review level.** `lean-proof` (inherited from [COM-C173](../C173/README.md), [COM-C174](../C174/README.md)).

**Prior art.** Verdict `known` (immediate). Restates COM-C173, COM-C174; finding reused from COM-C173 (this review: known), COM-C174 (this review: known). Sources: [OEIS A182206 (fetched 2026-11-04)](https://oeis.org/A182206): Coman's entry: Carmichael numbers divisible by 37 and 73; first term 294409 = 37*73*109; Greathouse (2012) notes they are 37*73*(72k+1) by Korselt; [OEIS A033502 (fetched 2026-11-04)](https://oeis.org/A033502): 294409 is the k = 6 Chernick number (6k+1)(12k+1)(18k+1); [OEIS A182206 (fetched 2026-11-04)](https://oeis.org/A182206): Coman's entry: Carmichael numbers divisible by 37 and 73; first term 294409 = 37*73*109; Greathouse (2012) notes they are 37*73*(72k+1) by Korselt. Searched: Coman's OEIS entries (author:Coman Carmichael, author:Coman pseudoprimes listings), web searches on the book title and the statement, reused search of the restated item(s) (2026-11-04).
