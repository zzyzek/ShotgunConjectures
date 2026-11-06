# OEIS A164754: a(n) = 4n^2 - 11n + 5 for n >= 3

**Source.** [A164754](https://oeis.org/A164754) (offset 2), R. H. Hardin, Aug 24 2009: number of n X 2 arrays with
entries 1..4, each value's cells connected, 1, 2, 3, 4 in the upper left, upper right, lower left and lower right
corners, "and with no element having more than 2 neighbors with the same value". Formulas in the entry, all marked
empirical: a(n) = 3a(n-1) - 3a(n-2) + a(n-3) for n >= 6, the g.f. x^2(1 + 5x + 4x^2 - 2x^3)/(1 - x)^3 (Colin
Barker, 2018), and a(n) = 4(n-2)^2 + 5(n-2) - 1 for n >= 3 (Bill McEachen, 2020). The scan record quotes an older
form, "Except for the first term, a(n)=4*n^2+13*n+8" (Vincenzo Librandi, May 26 2010), which is the same polynomial
with n shifted by 3. (OEIS text, CC BY-SA 4.0, revision #35 of Sep 01 2020, checked 2026-11-05.)

**Reading.** Rows 1..n, columns L (left) and R (right); neighbours are the 4-neighbours (same row other column, or
same column adjacent row), so a cell has at most 3 neighbours. "Connected" means connected under this adjacency.
Corners: (1,L) = 1, (1,R) = 2, (n,L) = 3, (n,R) = 4. This reading reproduces a(2..7) = 1, 8, 25, 50, 83, 124 by
brute force over all arrays (certificate/brute.py). Librandi's 4n^2 + 13n + 8 is the formula in the variable n - 3;
in the entry's indexing the claim is a(n) = 4n^2 - 11n + 5 = 4(n-2)^2 + 5(n-2) - 1 for n >= 3 (a(2) = 1 differs).

**Result.** True: a(n) = 4n^2 - 11n + 5 for every n >= 3. The recurrence and the g.f. follow.

**Argument.** Write c-cell for a cell of value c and c-path for a path of c-cells.

1. *Each value fills an interval in each column.* Let (i,j) and (k,j) be c-cells, i < r < k, and suppose (r,j) has
   value d != c. A c-path from (i,j) to (k,j) changes row by at most 1 per step, so it meets every row s with
   i < s < k in a c-cell. Hence in every such row whose cell in column j is not a c-cell, the other cell is a
   c-cell. Now follow d-paths from (r,j): from a cell (s,j) with i < s < k and value d, the other cell of row s is
   a c-cell, and (i,j), (k,j) are c-cells, so every d-cell reachable from (r,j) lies in column j strictly between
   rows i and k. Every value sits in a corner, in row 1 or row n, which is outside that range: the d-cells are not
   connected. Contradiction.
2. *Crossing values.* Say c crosses if it has cells in both columns, with row intervals I_L and I_R. (a) A c-path
   from a cell in L to a cell in R has a horizontal step, so I_L and I_R share a row. (b) If a shared row s is not
   an end of I_L, the cell (s,L) has three c-neighbours (above, below, beside), which is forbidden; the same for
   I_R. So every shared row is an end of both intervals.
3. *Converse.* An array with the corner values, interval columns and (a), (b) is counted: each value is one or two
   vertical segments joined in a shared row; a cell with three equal neighbours would have both vertical
   neighbours equal (interior of its interval) and the horizontal one equal (a shared row), against (b).
4. *Column words.* Reading top-down, column L is a block of 1s, then blocks of some of 2, 4, then a block of 3s;
   column R is 2s, some of 1, 3, then 4s. The middle values of either column cross. If c, c' both cross with shared
   rows s, s', then in each column the block of c lies above the block of c' iff s < s', so crossing values appear
   in the same order in both columns. This leaves nine word pairs (L word, R word): (13,24); (123,24), (143,24),
   (13,214), (13,234); (123,234), (143,214); (1243,24), (13,2134). (For example 1423 puts 4 above 2 in L, while R
   starts with 2 and ends with 4; and 2 in L together with 1 in R puts 1 above 2 in L and 2 above 1 in R.)
5. *Counting.* Let blocks have lengths as written, all >= 1.
   - (13,24): L = 1^a 3^(n-a), R = 2^b 4^(n-b), a, b in [1, n-1], nothing crosses: (n-1)^2.
   - (123,24): L = 1^a 2^c 3^d, R = 2^b 4^e. Value 2 has I_L = [a+1, a+c], I_R = [1, b]; a shared row is >= a+1 >= 2,
     so by (b) it is b, and then (a) and (b) hold exactly when b = a+1. Free: a + c + d = n, C(n-1,2) arrays.
     (143,24), (13,214), (13,234) are its images under the left-right and top-bottom mirrors (value maps 1<->2,
     3<->4 and 1<->3, 2<->4): C(n-1,2) each.
   - (123,234): L = 1^a 2^c 3^d, R = 2^b 3^e 4^f. Value 2 forces b = a+1 as above. Value 3 has I_L = [a+c+1, n],
     I_R = [b+1, b+e] with b+e <= n-1, so the shared row is a+c+1 = b+e, i.e. e = c, and then f = d-1 >= 1. Free:
     a + c + d = n with d >= 2, C(n-2,2) arrays. (143,214) is the left-right mirror: C(n-2,2).
   - (1243,24): L = 1^a 2^c 4^g 3^d, R = 2^b 4^e. Value 2 forces b = a+1; value 4 has I_L = [a+c+1, a+c+g],
     I_R = [b+1, n]. Row n is not in I_L, so by (b) the only shared row is b+1 = a+2; the shared rows are
     [max(a+c+1, a+2), a+c+g], and this equals {a+2} only for c = g = 1. Free: a + d = n-2, n-3 arrays.
     (13,2134) is the left-right mirror: n-3.
   Sum: (n-1)^2 + 4 C(n-1,2) + 2 C(n-2,2) + 2(n-3) = 4n^2 - 11n + 5 for n >= 3.

**Evidence.**
- Lean (Mathlib): [`A164754_mathlib.lean`](A164754_mathlib.lean). `a n` counts `f : Fin n × Bool → Fin 4` with
  `Valid f` (corners; every value connected under `Relation.ReflTransGen` of same-value 4-adjacent steps; no cell
  with three pairwise distinct neighbours of its value). Main theorem `A164754_formula : 3 ≤ n → (a n : ℤ) =
  4n^2 − 11n + 5`. Route: `valid_iff_model` and `a_eq_model` (steps 1-3, via `row_hit`, `column_interval`,
  `meet_of_valid`); `monoL`, `mono` (step 4: the left column reads 1, 2, 4, 3 and the right column 2, 1, 3, 4, with
  the left-right mirror `model_mir` for the right column); `tau`, `build`, `build_tau`, `tau_mem`, `model_build`,
  `tau_build`, `card_model` (arrays coded bijectively by their six block boundaries, subject to `cross1`..`cross4`);
  `card_T_eq_D`, `card_D`, `card_T` (step 5: the nine families and their sizes, via `pairs_card`, `square_card`,
  `line_card`). Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms of every theorem at most
  propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/brute.py`](certificate/brute.py): all arrays for n = 2..7 under the reading above; reproduces the
  entry's data.
- [`certificate/model.py`](certificate/model.py): for n = 2..7, every array is counted iff it satisfies the
  interval characterisation of steps 1-3 (no mismatch among all 16^(n-2) arrays).
- [`certificate/families.py`](certificate/families.py): the census by column-word pair of the brute-force
  solutions equals the nine family counts of step 5 for n = 3..7.
- [`certificate/count_model.py`](certificate/count_model.py): counts the interval characterisation over all column
  word pairs and block lengths for n = 2..16; equals 4n^2 - 11n + 5 (n >= 3) and Hardin's b-file
  ([`certificate/b164754.txt`](certificate/b164754.txt), n = 2..100).
- Outside Lean: none. Not verified in Lean: agreement of `a` with the OEIS data terms (brute.py computes a(2..7)
  from the same definition).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05. The OEIS entry and its history give the formula only as empirical (three
versions, 2010, 2016, 2020); no proof is linked. Not in google-deepmind/formal-conjectures (no
`FormalConjectures/OEIS/164754.lean`) or otoi-lab/oeis-lean-proofs (no file mentioning 164754). A web search found
no proof.
