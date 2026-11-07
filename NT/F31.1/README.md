# Guy UPINT F31 (Loxton–van der Poorten): the least multiplier can be quadratic in k

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section F31 (paraphrased): let L be the set of
integers with a base-4 representation using only the digits 0, 1, −1. Loxton and van der Poorten (Acta Arith. 49
(1987) 193–203) showed that for every odd k some m ≥ 1 has m ∈ L and km ∈ L, but their argument gives no estimate
of the least such m. Guy asks whether there is an absolute constant C with a multiplier below |k|^C, and quotes
k = 133 (m = 333) and k = 501 as examples needing large multipliers.

**Reading.** m(k) = least m ≥ 1 with m, km ∈ L, for odd k. Since L = −L, m(−k) = m(k); take k > 0.

**Result.** Partial; the polynomial-bound question stays open, but the exponent is pinned from below.
1. (New, all j.) For k_j = 2·4^j + 5 (j ≥ 1), every l ∈ L∖{0} with k_j·l ∈ L has at least 2j − 1 base-4 digits.
   Hence m(k_j) ≥ (2·4^(2j−2) + 1)/3 > k_j²/128 for j ≥ 3. So no C < 2 works: any bound m(k) ≤ |k|^C needs C ≥ 2.
2. (Data.) Exact m(k) for every odd k < 2·10^7. For 37 ≤ k < 2·10^7, m(k) < k²/48. The largest values of
   m(k)/k² come from k = 2·4^j + 5, where m(k_j) = (4^(2j+1) − 7·4^j + 48)/48 for 3 ≤ j ≤ 12 (so m/k² → 1/48),
   with digits (top first) +^j − 0^(j−3) +. The next family is k = 2·4^j − 5 (m/k² → 1/96).
3. (Lean.) m(133) = 333 and m(517) = 5425.

This suggests the answer to Guy's question is yes with C = 2 (conjecturally m(k) ≤ k²/48 for k ≥ 37), and that 2 is
optimal.

**Argument for 1.** Write l = A + 4^j B, where A holds the digits a_0..a_{j−1} (a_0 ≠ 0 after dividing out
powers of 4) and B the r = n − j remaining digits (r = 0 when l has at most j digits). Then
k_j l = 5l + 2·4^j l, and the base-4 carry chain of this sum runs over four consecutive blocks of positions: inputs
5a_i (positions i < j), 5b_i + 2a_i (positions j + i, i < r), 2a_i (positions j + i, r ≤ i < j) and 2b_i
(positions 2j + i, i < r), then zeros. An integer x is in L iff the forced chain x = d + 4x' (d ∈ {−1,0,1}
determined by x mod 4, failure on residue 2) never fails, and here every carry lies in {−2,…,2}; so k_j l ∈ L iff
the chain never meets residue 2 and the final carry is in {−1,0,1}. Indexing all four blocks by the digit index i
runs them in lockstep: a finite automaton on states (c₁, c₂, c₄, g₁, g₂) (three carries and the two guessed carries
at the block boundaries), reading (a_i, b_i) for i < r and a_i for r ≤ i < j; j enters only as the number of steps.
The state-set sequences are eventually periodic, so all (r, s = j − r) are covered by a finite computation:
acceptance happens only for s ∈ {0, 1}, i.e. n = j + r ≥ 2j − 1. The digit count n gives
|l| ≥ 4^(n−1) − (4^(n−1) − 1)/3.

**Evidence.**
- Lean (core): [`F31_1.lean`](F31_1.lean). `InL` is the source's definition (a digit list over {−1,0,1});
  `chk_complete` proves that the greedy checker `chk` accepts every element of L; `least_133`, `least_517`
  state m ∈ L, km ∈ L (explicit digit lists) and that no 1 ≤ m' < m works (kernel `decide +kernel` over `chk`).
  `tools/leancheck.sh`: OK, no warnings, axioms propext, Classical.choice, Quot.sound.
- [`certificate/family_lower.py`](certificate/family_lower.py): the automaton of the argument; prints the accepting
  (r, s) pairs (only s ≤ 1) and cross-checks the least digit count against direct search for j = 1..10.
- [`certificate/minm2.c`](certificate/minm2.c): exact m(k) by forward carry sets and a greedy top-down choice;
  agrees with [`certificate/brute.py`](certificate/brute.py) for all odd k ≤ 2001. Run on odd k < 2·10^7
  (46 s); record tables [`certificate/records_ratio.txt`](certificate/records_ratio.txt) (m/k²) and
  [`certificate/records_exponent.txt`](certificate/records_exponent.txt) (log m / log k);
  [`certificate/family_formula.txt`](certificate/family_formula.txt).
- Outside Lean: the all-j lower bound (paper reduction to the automaton plus the Python automaton computation),
  the family formula for 5 ≤ j ≤ 12, and the data range k < 2·10^7 (C program).

**Review level.** `lean-witness` for k = 133, 517; `rechecked` for the family lower bound (automaton computation
cross-checked against direct search for j ≤ 10).

**Prior art.** Checked 2026-11-07: web search (Loxton–van der Poorten 1987; Gonzalez, JTNB 4 (1992) 43–51, which
re-proves the existence theorem for general digit sets; OEIS A006288), formal-conjectures (nothing on F31). No
estimate of the least multiplier was found; Guy's k = 133 is the j = 3 member of the family. The quadratic lower
bound and the data appear new.
