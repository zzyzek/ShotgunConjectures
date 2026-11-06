# OEIS A195825: plateaus of the columns of the generalized pentagonal-number array

**Source.** [A195825](https://oeis.org/A195825) (Omar E. Pol, 2011): square array T(n,k), n ≥ 0, k ≥ 1, column k
built from the generalized (k+4)-gonal numbers as Euler's pentagonal number theorem builds the partition numbers
(column 1 = A000041, column 2 = A006950, column 3 = A036820). Comment (Pol, Jun 21 2012): "Conjecture: if k is odd
then column k contains (k+1)/2 plateaus whose levels are the first (k+1)/2 terms of A210843 and whose lengths are
k+1, k-1, k-3, k-5,... 2. Otherwise, if k is even then column k contains k/2 plateaus whose levels are the first k/2
terms of A210843 and whose lengths are k+1, k-1, k-3, k-5,... 3. The sequence A210843 gives the levels of the
plateaus of column k, when k -> infinity." [A210843](https://oeis.org/A210843): 1, 4, 13, 35, 86, ..., "Level of the
n-th plateau of the column k of the square array A195825, when k -> infinity." (OEIS text, CC BY-SA 4.0, A195825
revision #100 of Jun 28 2026, checked 2026-11-06.)

**Reading.** Column k has g.f. 1/Σ_{j∈ℤ} (−1)^j q^{(mj² − (m−2)j)/2} with m = k+2 (the entry's program; this
reproduces the data). A plateau is a maximal run of at least two equal consecutive terms.

**Result.** True. With m = k + 2:
- T(n+1, k) = T(n, k) exactly for A(m+1) ≤ n ≤ (A+1)(m−1) − 2, A ≥ 0. So the plateaus are n ∈ [A(m+1), (A+1)(m−1) − 1],
  of length k + 1 − 2A, for A = 0, 1, ... while k + 1 − 2A ≥ 2, and the column increases strictly elsewhere.
- The level of plateau A is T(A(k+3), k), the same for every k ≥ 2A + 1; so it is A210843(A+1). It equals
  Σ_{B ≤ A} p₃(B), with p₃ the 3-colored partition numbers A000716 (this also answers A210843's question: it is the
  Euler transform of 4, 3, 3, 3, ...).

**Argument.**
1. Jacobi's triple product gives Σ_j (−1)^j q^{(mj²−(m−2)j)/2} = Π_{n≥1} (1−q^{mn})(1−q^{mn−1})(1−q^{mn−m+1}), so
   T(n,k) counts partitions of n into parts ≡ 0, ±1 (mod m).
2. Removing one part 1: T(n+1) − T(n) = D(n+1), the number of such partitions of n+1 with no part 1.
3. A part ≠ 1 is am + e with a ≥ 1, e ∈ {−1, 0, 1}, so lies in [a(m−1), a(m+1)]; a sum of such parts lies in
   [A(m−1), A(m+1)] with A = Σa ≥ 1, and conversely every n in such an interval is A parts from {m−1, m, m+1}. So
   D(n) = 0 iff n lies in a gap A(m+1) < n < (A+1)(m−1), which has m − 2 − 2A elements; a gap of g zeros is a
   plateau of length g + 1 = k + 1 − 2A.
4. Level of plateau A: N = A(m+1). In a partition of N, the parts am + e ≠ 1 have Σa ≤ A when 2A + 3 ≤ m
   (Σa(m−1) ≤ N). The map am + e ↦ a(m+1) + e, refilling with 1s up to A(m+2), is a bijection onto the partitions of
   A(m+2) into parts ≡ 0, ±1 mod m+1 (the inverse direction uses Σa·m ≤ A(m+2) and each part ≤ a(m+2)). So the
   level does not depend on m; it counts multisets of pairs (a, e) with Σa ≤ A, which is Σ_{B≤A} p₃(B).

**Evidence.**
- Lean (Mathlib): [`A195825_mathlib.lean`](A195825_mathlib.lean), with T(n,k) modelled as the number of partitions
  (`Nat.Partition`) into parts ≡ 0, ±1 mod m. Main theorems `flat_iff` (steps 2-3: exact set of n with
  T(n+1) = T(n)) and `level_const` (step 4: the level of plateau A is the same for all k ≥ 2A + 1); route `T_succ`,
  `D_pos_iff`, `level_step` with the bijection `Φ`/`Ψ`. Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings;
  axioms at most propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): for k = 1..40 and n ≤ 1500, the entry's series equals the
  partition count (step 1), the plateaus are exactly as stated, the levels are Σ_{B≤A} p₃(B); the entry's data and
  A210843's 15 data terms are reproduced.
- Outside Lean: step 1 (Jacobi triple product for these products; checked 2026-11-06: Mathlib has only Euler's
  pentagonal number theorem, `Mathlib/Combinatorics/Enumerative/Pentagonal`, i.e. the column k = 1, and no triple product), and the closed form Σ p₃(B) of the levels (not
  needed for the conjecture; checked numerically).

**Review level.** `lean-witness` (all combinatorics in Lean; the triple product step is outside).

**Prior art.** Checked 2026-11-06. The entry (revision #100, 2026) still states the conjecture; A210843 asks
whether it is the Euler transform of 4, 3, 3, ... (step 4 answers yes). The triple product and the reading of the
columns as partitions into parts ≡ 0, ±1 mod m are classical; no proof of the plateau structure was found (web
search). Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
