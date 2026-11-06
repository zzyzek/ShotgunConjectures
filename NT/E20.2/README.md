# Guy E20: N_5(7) = 37

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section E20 (Davenport–Schinzel sequences, Table 8). N_d(n) is the greatest length of a sequence on n letters with no two equal adjacent terms and no alternating subsequence a b a b … of length d + 1. Guy asks to extend the table; OEIS A005280 (N_5) and A005281 (N_6) stop at n = 6.

**Result.** N_5(7) = 37 (new term of A005280; Peterkin's bound 7n − 13 gives 36). A maximal sequence:
1 2 3 2 4 2 5 2 6 2 6 5 6 4 6 3 6 7 6 7 3 7 4 7 5 7 1 7 1 5 1 4 1 3 1 2 1

**Argument.** Lower bound: the sequence above. Upper bound: exhaustive memoised search. The future of a sequence depends only on its letters ordered by last occurrence and, for every pair, the number of blocks of its restriction to that pair; appending the letter of recency rank i adds one block to its pairs with every more recent letter and none to the others. So the maximum remaining length is a function of this state, and a memoised search over all reachable states (25 613 680 for d = 5, n = 7, letters relabelled by recency) gives the exact maximum.

**Evidence.**
- Lean (core): [`E20_2.lean`](E20_2.lean), `E20_2_main`: the 37-term sequence is a degree-5 DS sequence on letters 1..7, so N_5(7) ≥ 37. Axioms propext, Quot.sound. Outside Lean: N_5(7) ≤ 37 (the search below).
- `certificate/ds.cpp` (C++, open-addressing table, 0.6 GB, 9 s) and `certificate/ds.py` (same recursion in Python). Both reproduce N_4(n) for n ≤ 8, N_5(5) = 22, N_5(6) = 29, N_6(5) = 34; ds.cpp reproduces N_6(6) = 46 (`N6_6.out`) and gives N_5(7) = 37 (`N5_7.out`, with the witness, rechecked by an independent Python test of adjacency and pair-block counts).
- N_6(7) is out of reach of this method here (about 150 times more states than N_6(6)'s 2.7·10^7).

**Review level.** `lean-witness` (lower bound in Lean; upper bound by computer search, validated on the known values).

**Prior art.** OEIS A005280 (last edit 2021) lists n ≤ 6 only; no table beyond n = 6 found on the web or arXiv (searches for exact λ_4(n) values); formal-conjectures has no entry. 2026-11-06.
