# OEIS A078130: numbers with exactly one representation as a sum of cubes > 1 — last term 218

**Source.** [A078130](https://oeis.org/A078130) (offset 1), "Numbers having exactly one representation as sum of
cubes > 1", i.e. A078128(n) = 1. Comment: "Conjecture: the sequence is finite; is a(63)=218 the last entry?"
(OEIS text, CC BY-SA 4.0.) Revision #25 (Jun 18 2025) answers "Yes" with a sketch by Sean A. Irvine and adds the
keywords fini, full.

**Result.** True. The numbers n ≥ 1 with exactly one partition into cubes k³, k ≥ 2, are the 63 data terms
8, 16, …, 210, 218; so the set is finite and a(63) = 218 is the last term.

**Argument.**
1. Only 8 and 27: every r ≥ 182 is 8x + 27y (y = 3r mod 8, x = (r − 27y)/8; 181 = 8·27 − 8 − 27 is the Frobenius
   number). If n ≥ 216m + 182, write n − 216m = 8x + 27y; then x + 27j eights and y + 8(m − j) twenty-sevens,
   j = 0..m, are m + 1 different partitions of n into cubes > 1. With m = 1: A078128(n) ≥ 2 for n ≥ 398.
2. For n < 512 the possible parts are 8, 27, 64, 125, 216, 343, and a partition is fixed by its multiplicities, so
   A078128(n) equals the coin-change count with these six coins. Evaluating it for n ≤ 397 gives A078128(n) ≥ 2 for
   219 ≤ n ≤ 397 and A078128(n) = 1 for n ≤ 218 exactly at the 63 data terms.

**Evidence.**
- Lean (Mathlib): [`A078130_mathlib.lean`](A078130_mathlib.lean), namespace `A078130`. `a n` is the number of
  `p : Nat.Partition n` whose parts are all cubes k³ with k ≥ 2 (the OEIS definition); `IsA078130 n := 1 ≤ n ∧ a n = 1`.
  Theorems: `A078130_iff` (IsA078130 n ↔ n ∈ S, S the 63 data terms), `A078130_finite`, `A078130_le` (every term
  ≤ 218), `A078130_ncard` (63 terms), `A078130_nth` (`Nat.nth IsA078130 62 = 218`). Route: `card_msets`,
  `mem_msets` (coin-change count = number of multisets), `a_eq_ways` (n < 512), `a_lower` (step 1), kernel
  evaluation (`decide +kernel`) of the coin-change counts for n < 398.
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings. Axioms: at most propext, Classical.choice, Quot.sound.
  No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): recomputes A078128 by the generating function, checks the
  8/27 bound, the 63 terms, and agreement with the b-file b078128.txt (n ≤ 10000; all agree, run 2026-11-06).
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. Known: the entry (revision #25, Jun 2025) answers the question with Irvine's
argument (trade 4³ for eight 2³; residue classes mod 8 from known representations); A078129 (Adams-Watters 2006) has
the 8/27 Frobenius argument for representability. Not in google-deepmind/formal-conjectures (clone of 2026-11-05) or
otoi-lab/oeis-lean-proofs (clone of 2026-10-13). This directory gives a Lean proof against the partition definition.
