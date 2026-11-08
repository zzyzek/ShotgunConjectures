# OEIS A225563: no totient trajectory splits into an odd number of equal-sum sets

**Source.** [A225563](https://oeis.org/A225563), Kevin L. Schwartz and Christian N. K. Anderson, May 10 2013:
numbers whose totient trajectory can be partitioned into two sets with the same sum. Comment in the entry:
"Conjecture: No totient-trajectory can be partitioned into an odd number of sets with the same sum."
(OEIS text, CC BY-SA 4.0, cached entry read 2026-11-08.)

**Reading.** The totient trajectory of m >= 1 is m, phi(m), phi(phi(m)), ..., 1 (its entries are distinct).
"An odd number of sets" means k >= 3 odd; k = 1 is the trivial one-set partition.

**Result.** True, and more: for every m >= 1 and every k >= 3 the trajectory has no partition into k sets of
equal sum. The trajectory sum is at most 3m - 3 for m >= 2 (equality at m = 2, 3, 5, 17, 257, 65537).

**Argument.** For even x, the integers below x coprime to x are odd, so phi(x) <= x/2. For x >= 3, phi(x) is
even. So after the first step the trajectory is phi(m) = a_1 > a_2 > ... with a_{i+1} <= a_i/2 until 2, then 1,
and a_1 + a_2 + ... <= 2 a_1 - 1 (induction). With a_1 = phi(m) <= m - 1 the total sum S satisfies
S <= m + 2(m - 1) - 1 < 3m. In a partition into k parts of sum s each, the part containing m has s >= m, so
S = ks >= 3m. Contradiction.

**Evidence.**
- Lean (Mathlib): [`A225563_mathlib.lean`](A225563_mathlib.lean). `traj n` is the trajectory as a list; a
  partition is a list of k lists whose concatenation is a permutation of `traj n`, each summing to s (empty
  parts allowed). Main theorems `A225563_no_partition` (n >= 1, k >= 3: impossible) and `A225563_conjecture`
  (k odd, k != 1). Lemmas `two_mul_totient_le`, `traj_sum_even`, `traj_sum_lt`. Axioms propext,
  Classical.choice, Quot.sound.
- `certificate/bound.py`: numerical check of S <= 3m - 3 for m <= 10^6 (max S/m = 2.99995).
- Outside Lean: none. Reading the entry's words "partitioned into an odd number of sets" as the list
  formulation above is the only step not in Lean.

**Review level.** lean-proof.

**Prior art.** Checked 2026-11-08: OEIS entry (conjecture stands as a comment), google-deepmind/formal-conjectures
(no OEIS/225563 file), otoi-lab/oeis-lean-proofs (no file), web search. No proof found. The argument is
elementary and short; the entry's own comment that trajectory entries other than the first and last are even is
the starting point.
