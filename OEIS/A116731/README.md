# OEIS A116731: bubble sort produces (n^3 − 3n^2 + 5n)/3 distinct (flips, iterations) pairs

**Source.** [A116731](https://oeis.org/A116731), "Number of permutations of length n which avoid the patterns
321, 2143, 3124; or avoid the patterns 132, 2314, 4312, etc." Comment: "Conjecture: also counts the distinct
pairs (flips, iterations) that a bubble sort program generates when sorting all permutations of 1..n. [From
Wouter Meeussen, Dec 13 2008]". Formula (Franklin T. Adams-Watters, 2006): a(n) = (n^3 − 3n^2 + 5n)/3; the
entry's g.f. comes from L. Pudwell, *Systematic Studies in Pattern Avoidance* (2005). (OEIS text, CC BY-SA
4.0, checked 2026-11-06.)

**Reading.** Bubble sort: repeat left-to-right passes swapping adjacent out-of-order entries until a pass makes
no swap. Flips = total swaps; iterations = number of passes that swapped. Counting the final no-swap pass too,
or shrinking the scanned range after each pass, gives the same number of distinct pairs (each is an injective
relabelling of the pairs; `certificate/check.py` confirms all four variants for n ≤ 9). The Meeussen program is
not in the entry; this is the standard algorithm.

**Result.** True for every n ≥ 1: the pairs are exactly (0, 0) and (i, b) with 1 ≤ b ≤ n − 1 and
b ≤ i ≤ M(b), where M(b) = Σ_{j<n} min(b, j); there are (n^3 − 3n^2 + 5n)/3 of them.

**Argument.** Let c(v) be the number of entries greater than v to the left of v. One pass lowers every
positive c(v) by exactly 1 (the running maximum carried right is greater than v exactly when c(v) > 0, and it
jumps over v) and makes one swap per v with c(v) > 0. Hence iterations = b = max c(v) and flips = Σ c(v)
(the inversion number). Since c(v) ≤ n − v, b ≤ Σ c ≤ Σ_v min(b, n − v) = M(b) and b ≤ n − 1. Conversely every
table c with c(v) ≤ n − v is realised (insert n, n−1, …, 1, putting v at position c(v) among the larger
values), and a greedy table with c(1) = b, c(v) ≤ min(b, n − v) reaches every total i in [b, M(b)]. With
2M(b) = 2bn − b^2 − b, Σ_{b<n} (M(b) − b + 1) = (n^3 − 3n^2 + 5n)/3 (the b = 0 term is the pair (0, 0)).

**Evidence.**
- Lean (Mathlib): [`A116731_mathlib.lean`](A116731_mathlib.lean). `pass`, `bubbleAux`, `bubble` are the
  algorithm on lists; `cgb v l` = c(v). Theorems: `pass_cgb`, `pass_swaps` (one pass), `bubble_eq`
  (bubble l = (Σ c, max c)), `bubble_mem_P`, `P_sub`, `pairs_eq_P` (the set of pairs over
  `(List.range' 1 n).permutations` is `P n`), `card_P_closed`, and `A116731_conjecture`: for n ≥ 1,
  `((List.range' 1 n).permutations.map bubble).toFinset.card = (n^3 + 5n − 3n^2)/3`.
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms propext, Classical.choice, Quot.sound. No
  `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): pair counts for four loop variants, n ≤ 9; the
  (Σ c, max c) identity on every permutation, n ≤ 9; pattern-class counts Av(321, 2143, 3124) = formula, n ≤ 8.
- Outside Lean: that A116731 as defined (the pattern class) equals (n^3 − 3n^2 + 5n)/3 for all n (entry formula
  and g.f., Pudwell 2005; checked n ≤ 8 by check.py); the reading of "a bubble sort program".

**Review level.** `lean-proof` for the bubble-sort count; the pattern-class formula is cited.

**Prior art.** Checked 2026-11-06. The entry (current revision) still lists the statement as a conjecture.
Web search (bubble sort, distinct (swaps, passes) pairs) found nothing; recent papers citing A116731
(Eğecioğlu–Gaiser–Yin arXiv:2607.20750, Striker–Tenner arXiv:2603.17287) do not mention bubble sort. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (trees at HEAD 2026-11-06). The facts "passes
= max inversion-table entry" and "swaps = inversions" are classical (Knuth, TAOCP vol. 3, 5.2.2); the pair-set
count is ours.
