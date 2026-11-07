# OEIS A082108: a(n−1) is the largest integer keeping the partial sum below 1

**Source.** [A082108](https://oeis.org/A082108) (offset 0): a(n) = 4n² + 6n + 1. The 2013 wiki conjecture list gives
"Conjecture. a(n-1) is the largest integer such that Sum[a(k)/(2k)!, k=1,2,...,n] is less than 1". The current entry
no longer carries the conjecture; it has, from Robert Israel (Jul 19 2017), "Sum_{k=1..n} a(k-1)/(2*k)! = 1 - 1/(2*n)!".
(OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** Literally (summand a(k)) the claim fails at n = 1: a(1)/2! = 11/2 > 1. The intended statement has summand
a(k−1): a(n−1) is the largest integer x with Σ_{k=1}^{n−1} a(k−1)/(2k)! + x/(2n)! < 1.

**Result.** The intended statement is true; it is equivalent to Israel's formula.

**Argument.** a(k−1)/(2k)! = 1/(2k−2)! − 1/(2k)! because (2k)(2k−1) − 1 = 4(k−1)² + 6(k−1) + 1; the sum telescopes
to 1 − 1/(2n)!. With S = 1 − 1/(2n−2)!, S + x/(2n)! < 1 iff x < (2n)(2n−1) = a(n−1) + 1.

**Evidence.**
- Lean (Mathlib): [`A082108_mathlib.lean`](A082108_mathlib.lean), indices shifted by one. `A082108_partial_sum`
  (Israel's formula), main theorem `A082108_isGreatest` (IsGreatest of the set of such integers is a(n)),
  `A082108_literal_false`. Check OK, no warnings; axioms propext, Classical.choice, Quot.sound.
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: Israel's 2017 formula in the entry implies the statement (one line). Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
