# Guy UPINT E22: Gupta's rosary bound m(n) ≤ ⌊n²/2⌋ for odd n (case n = 7)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section E22 (paraphrased): m(n) is the least
length of a cycle a_1, ..., a_m with entries in [1, n] such that every permutation of 1..n is a subsequence of some
rotation a_j, ..., a_m, a_1, ..., a_(j-1). Gupta conjectured m(n) ≤ ⌊n²/2⌋.

**Result.** Partial (new data point). m(7) ≤ 24 = ⌊49/2⌋: the cycle
W = 2 5 1 6 7 3 5 1 2 4 7 6 1 5 3 7 4 2 1 5 6 7 3 4
contains every permutation of 1..7 in some rotation. The conjecture is proved for even n (Lecouturier-Zmiaikou,
Discrete Math. 312 (2012)); for odd n they give m(n) < n²/2 + n/4 - 1, i.e. m(7) ≤ 25, and OEIS A373728 lists
m(n) only for n ≤ 6 (2, 4, 8, 12, 17). The general odd case stays open; n = 3, 5 are covered by A373728.

A 15-minute tabu search for length 23 found nothing (inconclusive).

**Argument.** Direct check of all 5040 permutations against the 24 rotations of W.

**Evidence.**
- Lean (Mathlib, only for `List.Perm` API): [`E22_1_mathlib.lean`](E22_1_mathlib.lean), namespace `NT_E22_1`.
  Main theorem `rosary7`: every p with p ~ [1..7] is a `List.Sublist` of `rot W j` for some j < 24 = W.length.
  The check `all_covered` runs in the kernel (`decide +kernel`) over a structurally recursive permutation list
  `perms`, whose completeness (`mem_perms`) and the soundness of the Boolean subsequence test (`isSubseq_sound`)
  are proved. Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext, Quot.sound.
- [`certificate/tabu.c`](certificate/tabu.c): the tabu search that found W (n = 6, length 17 is found as a check);
  [`certificate/check.py`](certificate/check.py): independent check from the definition.
- Outside Lean: nothing for the n = 7 bound; the odd-n conjecture in general is open.

**Review level.** `lean-proof` for m(7) ≤ 24.

**Prior art.** Checked 2026-11-06: Lecouturier-Zmiaikou 2012 (arXiv:1009.5106); OEIS A373728 (no n = 7 value);
the 2021 superpattern paper (arXiv:2108.05474) refutes a different Gupta conjecture (bidirectional
circular superpatterns, 3k²/8 + O(k)) and gives the lower bound n²/2 - n^(7/4+o(1)) for the bidirectional version.
Not in google-deepmind/formal-conjectures (clone 2026-11-06).
