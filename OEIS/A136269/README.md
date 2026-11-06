# OEIS A136269: a(3k) = (3/4)10^(4k) + 5*10^(k-1) - 1

**Source.** [A136269](https://oeis.org/A136269) (offset 0), Cino Hilliard, Mar 19 2008: "Floor of sum of the first
10^n cube roots." Comment: "Conjecture: For n = 3k, a(n) = (3/4)*10^(4n/3)+5*10^(n/3-1)-1." A later comment (Sela
Fried, Oct 02 2024) states that the conjecture is true, with links to a note and to arXiv:2410.07237. (OEIS text,
CC BY-SA 4.0, revision #14 of Oct 14 2024, checked 2026-11-06.)

**Reading.** a(n) = floor(Sum_{i=1..10^n} i^(1/3)) with real cube roots. For k = 0 the formula gives 1/4, not an
integer (a(0) = 1), so the claim is for k >= 1.

**Result.** True for every k >= 1. More generally, for every even M >= 2,
floor(Sum_{i=1..M^3} i^(1/3)) = 3M^4/4 + M/2 - 1; the case M = 10^k is the conjecture.

**Argument.** Let H(c) = (3/4)c^4 + (1/2)c and, for i >= 1, a = (i-1)^(1/3), b = i^(1/3), so b^3 - a^3 = 1.
1. *One step.* Using b^3 - a^3 = 1, E_i = H(b) - H(a) - b = (b-a)^3 (a+b)/4 (polynomial identity after
   multiplying (a+b)/2 by b^3 - a^3). So E_i > 0, and E_1 = 1/4.
2. *Small steps.* For i >= 2, a >= 1. From (b-a)(a^2+ab+b^2) = 1 and a^2+ab+b^2 >= 3ab, (b-a)ab <= 1/3. Hence
   E_i = (b-a)^3(a+b)/4 <= (b-a)(a+b)/(36 a^2 b^2) = (1/a^2 - 1/b^2)/36.
3. *Telescoping.* With c = N^(1/3), Sum_{i<=N} i^(1/3) = H(c) - Sum E_i, and 1/4 <= Sum E_i <= 1/4 + (1 - 1/c^2)/36.
   So H(c) - 1/4 - 1/36 <= S(N) <= H(c) - 1/4.
4. For N = M^3, c = M and H(M) = 3M^4/4 + M/2 is an integer when M is even; S(N) lies in (H - 1, H), so the floor
   is H - 1. For M = 10^k: 3*10^(4k)/4 + 5*10^(k-1) - 1.

**Evidence.**
- Lean (Mathlib): [`A136269_mathlib.lean`](A136269_mathlib.lean). Definitions: `cr i = (i:ℝ)^(1/3:ℝ)`,
  `S N = Σ_{i<N} cr (i+1)`, `A136269 n = ⌊S (10^n)⌋`. Main theorem `OEIS136269.A136269_conj : 1 ≤ k →
  (A136269 (3k) : ℝ) = 3/4 * 10^(4k) + 5 * 10^(k-1) - 1`. Also `floor_sum_cube_even` (all even M ≥ 2) and
  `sum_bounds` (step 3 for all N ≥ 1). Route: `step` (steps 1-2), `sum_bounds`, `cube_bounds`. Check:
  `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext, Classical.choice, Quot.sound. No
  `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): direct sums for n <= 6 match the data; the formula matches the
  data for n = 3, 6, 9, 12, 15; the bounds of step 3 hold for M <= 60.
- Outside Lean: none. Not verified in Lean: agreement with the OEIS data (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. Proved by Sela Fried (2024), "On the partial sums of Sum n^s for 0 < s < 1"
(note linked from the entry) and arXiv:2410.07237, p. 3; the entry records it as true. The proof here (telescoping
with an explicit trapezoid excess) is self-contained. No Lean proof found: not in google-deepmind/formal-conjectures
(no `FormalConjectures/OEIS/136269.lean`) or otoi-lab/oeis-lean-proofs.
