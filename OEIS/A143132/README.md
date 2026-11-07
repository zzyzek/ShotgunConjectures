# OEIS A143132: last digits cycle 1, 6, 6, 6

**Source.** [A143132](https://oeis.org/A143132), binomial transform of [1, 5, 15, 35, 70, 0, 0, ...] (offset 0).
Comment: "Conjecture: rightmost digit of terms is cyclic: (1, 6, 6, 6, ... repeat)." (OEIS text, CC BY-SA 4.0,
revision #7 of Feb 08 2022, checked 2026-11-07.)

**Result.** True: a(n) mod 10 = 1 if 4 | n, and 6 otherwise.

**Argument.** a(n) = C(n,0) + 5C(n,1) + 15C(n,2) + 35C(n,3) + 70C(n,4). By Vandermonde,
C(n+40,k) = C(n,k) + sum_{j=1..k} C(40,j)C(n,k-j), and C(40,1), C(40,2), C(40,3), C(40,4) = 40, 780, 9880, 91390 are
all divisible by 10. So a(n+40) = a(n) mod 10, and the 40 residues n < 40 give the pattern (period 4 divides 40).
(Mod 5 alone, a(n) = 1 always since c = (1,0,0,0,0) mod 5.)

**Evidence.**
- Lean (Mathlib): [`A143132_mathlib.lean`](A143132_mathlib.lean), main theorem `A143132.A143132_last_digit`:
  `a n % 10 = if n % 4 = 0 then 1 else 6` for every n, where `a n = sum_{k<=n} n.choose k * c k` is the entry's
  definition. Axioms propext, Classical.choice, Quot.sound.
- `certificate/check.py`: the definition reproduces the 34 data terms; the pattern holds for n < 10^4.
- Outside Lean: none (agreement of the definition with the data terms is checked by the script only).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-07: entry and history (revisions #1-#7) give no proof; not in
google-deepmind/formal-conjectures (FormalConjectures/OEIS) or otoi-lab/oeis-lean-proofs. The argument is a routine
periodicity check; it is not claimed as deep.
