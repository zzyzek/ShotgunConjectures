# OEIS A082981: the six section conjectures

**Source.** [A082981](https://oeis.org/A082981) (John W. Layman, May 28 2003): start with S(0) = {1,1}; S(k) =
I(S(k-1)), where I inserts a(i)+a(i+1) between a(i) and a(i+1) whenever 4a(i+1) <= 5a(i); the sequence is the limit
of S(k). Conjectures in the entry: (1) a(2n+1) is A077442 ("2*a(n)^2 + 7 is a square"); (2) a(4n+1) is A038761;
(3) a(4n+2) is A077444 ("numbers k such that (k^2 + 4)/2 is a square"); (4) a(4n+2)/2 is A002315; (5) a(4n+4) is
A005319; (6) a(4n+4)/4 is A001109. Also "It appears that a(n) = 6*a(n-4) - a(n-8)" and Colin Barker's empirical
g.f. (OEIS text, CC BY-SA 4.0, revision #22 of Dec 24 2025, checked 2026-11-06.)

**Reading.** "ax^2+7" in conjecture (1) is a typo for 2x^2+7 (the A077442 definition). Offsets: A077442,
A038761, A002315, A005319, A001109 have offset 0, A077444 offset 1; so the claims are a(2n+1) = A077442(n),
a(4n+1) = A038761(n), a(4n+2) = A077444(n+1), a(4n+2)/2 = A002315(n), a(4n+4) = A005319(n+1), a(4n+4)/4 =
A001109(n+1) for n >= 0. A077442 and A077444 are read as their definitions (increasing enumerations of the
solution sets), so (1) and (3) include that the sections hit every solution.

**Result.** All six are true. Moreover a(4j+t) = 4c_j + t d_j (t = 1..4, with 4c_{j+1} = 4c_j + 4d_j for t = 4),
where (c_0, d_0) = (0, 1) and (c, d) -> (c + d, 4c + 5d); this gives a(n) = 6a(n-4) - a(n-8) and the g.f.

**Argument.**
1. *Locality.* I acts on each adjacent pair separately, so the list grown from a pair (x, y) satisfies
   F_{k+1}(x,y) = F_k(x, x+y) ++ tail F_k(x+y, y) if 4y <= 5x, and F_k(x,y) = [x, y] for all k otherwise.
2. *Leftmost live pair.* If x < 4y <= 5x the pair (x, x+y) is dead, so F_{k+1}(x,y) = x :: F_k(x+y, y). If
   4y <= x, F_k(x, x+y) is a prefix of F_{k+1}(x,y).
3. *Blocks.* For A < d (and 4d <= 5A when starting at A itself), the pairs (A + id, d), i = 0..3, are in the first
   case and output A, A+d, A+2d, A+3d; the pair (A+4d, d) is in the second case and hands over to the pair
   (A', d') = (A+4d, A+5d), which again has A' < d' and 4d' <= 5A'. Starting from (1,1) = (0 + 1, 1), the stable
   prefix of S(k) is 1, 2, 3, 4, 9, 14, 19, 24, 53, ..., with A_j = 4c_j, d_j as above.
4. *Recurrences.* (c, d) -> (c + d, 4c + 5d) has trace 6 and determinant 1, so c_j, d_j and every fixed linear
   combination satisfy x(j+2) = 6x(j+1) - x(j). This gives (2) 4c+d, (4) 2c+d, (5) 4c, (6) c from the first two
   terms.
5. *Pell sets.* d^2 - 4cd - 4c^2 = 1 for all j. Then 2(4c+d)^2 + 7 = (3d-2c)^2, 2(4c+3d)^2 + 7 = (2c+5d)^2 and
   (4c+2d)^2 + 4 = 2(2d)^2. Conversely, a solution of 2x^2 + 7 = y^2 with x >= 6 descends to (3x - 2y, 3y - 4x),
   a smaller positive solution; by induction it is 4c_j + d_j or 4c_j + 3d_j, and x = 3x' + 2y' is then
   4c_{j+1} + d_{j+1} or 4c_{j+1} + 3d_{j+1}; x <= 5 leaves x = 1, 3. Likewise k^2 + 4 = 2y^2 with k >= 6 descends
   to (3k - 4y, 3y - 2k), and k <= 5 leaves k = 2. The sections are strictly increasing, so they are the
   increasing enumerations of the solution sets: (1) and (3).

**Evidence.**
- Lean (Mathlib): [`A082981_mathlib.lean`](A082981_mathlib.lean). `ins` is I on lists, `S k = ins^[k] [1,1]`.
  `A082981_limit : 1 ≤ n → ∃ K, ∀ k ≥ K, (S k)[n-1]? = some (a n)` (the limit exists and is `a`); `a_block`;
  `conj1` (`a (2n+1) = A077442 n`, `A077442 n = Nat.nth (fun x => IsSquare (2x^2+7)) n`), `conj2`, `conj3`
  (`a (4n+2) = A077444 (n+1)`, `A077444 n = Nat.nth (fun k => 2 ∣ k^2+4 ∧ IsSquare ((k^2+4)/2)) (n-1)`),
  `conj4`, `conj5`, `conj6` (A038761, A002315, A005319, A001109 defined by their recurrences). Route: `iter_split`,
  `F_alive`, `F_dead`, `PF_step1`, `PF_step2`, `PF_tv`; `cd_inv`, `c_rec`, `d_rec`, `rec_eq`; `sol1_complete`,
  `sol3_complete`, `nth_eq`. Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext,
  Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): the process run to depth 60 (stable prefix of 49 terms) agrees
  with the b-file ([`certificate/b082981.txt`](certificate/b082981.txt), n = 1..1000); the block formula equals
  the b-file; the six claims for n < 240; the solution sets of 2x^2+7 = square and (k^2+4)/2 = square below 10^7
  equal the sections.
- Outside Lean: none. Not verified in Lean: that the recurrence definitions of A038761, A002315, A005319, A001109
  match those entries (each entry states that recurrence with these initial terms) and agreement with the data
  terms (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry and its history (to #22, Dec 24 2025) keep the six conjectures and
the recurrence as conjectural. Layman's linked note "Ratio-Determined Insertion Sequences and the Tree of their
Recurrence Types" (2003) lists this sequence with recurrence type {6,4} among conjectures, without proof. Not in
google-deepmind/formal-conjectures (no file for 082981) or otoi-lab/oeis-lean-proofs. A web search found no proof.
