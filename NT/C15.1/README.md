# Guy UPINT C15: Selfridge's conjecture on k(m) for even m (partial)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section C15 (paraphrased): k(m) is the
largest number of distinct residues mod m with no nonempty subset summing to 0 mod m. For m = 2(l² + l + 1)
Selfridge gives a set of size 2l + 1 = √(2m − 3), and he conjectures that for every even m his set, or that set with
one element deleted, is best possible. In the form used by later authors (e.g. *Additive Combinatorics: A Menu of
Research Problems*, arXiv:1705.07444, problem on the Olson constant): k(m) = ⌊√(2m − 3)⌋ for every even m.
That source reports a verification by Subocz for even m ≤ 64.

**Result (partial; the conjecture stays open).** k(m) = ⌊√(2m − 3)⌋ for every even m with 6 ≤ m ≤ 100.

**Argument.** For each even m let K = ⌊√(2m − 3)⌋. `certificate/zsfdec.c m T` decides whether Z_m has a
zero-sum-free set of T distinct nonzero residues by depth-first search over increasing residues, keeping the set
of nonempty subset sums as a bitset (x may be added iff −x is not already a subset sum). Symmetry: if the set
contains a unit u, multiplying by u⁻¹ gives a zero-sum-free set of the same size containing 1, so the search
covers (A) sets containing 1 and (B) sets of non-units only. For every even m in [6, 100] the program finds a set
of size K (a lower-bound witness, printed) and proves that no set of size K + 1 exists (both cases exhausted).
`certificate/results.txt` lists the 48 runs with node counts; m = 100 took 352 s (8.2·10^8 nodes).
Cross-check: for 6 ≤ m ≤ 59 the values agree with an independent full enumeration of all zero-sum-free sets
(`scratch/nt-CD/c15_zsf.c` in the scan repo) and with Guy's statement that k = ⌊(−1 + √(8m + 9))/2⌋ for
5 < m < 24 where the two formulas agree.

**Evidence.** `certificate/zsfdec.c`, `certificate/run.sh`, `certificate/results.txt`. No Lean file: proving
nonexistence needs the full search tree (about 10^9 nodes at m = 100), beyond kernel evaluation. Outside Lean: the
whole computation (run 2026-11-07, single core, about 40 min in total).

**Review level.** `agent` (computation, cross-checked against an independent program for m ≤ 59 and against
Subocz's published range m ≤ 64).

**Prior art.** Checked 2026-11-07: Balandraud (2012) settled the prime case (Selfridge's prime conjecture); for
even m the conjecture is listed as open in arXiv:1705.07444 with verification to 64. The new part here is
66 ≤ m ≤ 100. Not in google-deepmind/formal-conjectures (clone of 2026-11-06).
