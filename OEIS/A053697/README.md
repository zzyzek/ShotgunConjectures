# OEIS A053697: the two six-step families of the base-11 inverse-digit map are invariant (the global claim is open)

**Source.** [A053697](https://oeis.org/A053697): a(n+1) = a(n) + a^(n), addition in base 11, where a^(n) replaces
each digit of a(n) by its inverse mod 11, zero digits deleted. "Conjecture. For any positive integer a(1), the
sequence ... eventually cycles through the forms a(k)=[1][4^a][3][(84)^b],..., a(k+6)=[1][4^a][3][(84)^(b+1)], or
through a(k)=[1][5^a][4][(84)^b],..., a(k+6)=[1][5^a][4][(84)^(b+1)], for nonnegative integers a and b."
(OEIS text, CC BY-SA 4.0, fetched 2026-11-07.)

**Result (partial).**
- The two families are exactly as claimed, for all a, b >= 0: six steps take [1][4^a][3][(84)^b] to
  [1][4^a][3][(84)^(b+1)] through 2 7^a (84)^b 7, 9 5^a 4 (84)^b, 1 4^a 3 (84)^b 7, 2 7^a (84)^(b+1),
  9 5^a 4 (84)^b 7; and [1][5^a][4][(84)^b] (a >= 1) to [1][5^a][4][(84)^(b+1)] through 3 4^(a-1) 3 (84)^b 7,
  7^a (84)^(b+1), 1 5^a 4 (84)^b 7, 3 4^(a-1) 3 (84)^(b+1), 7^a (84)^(b+1) 7. (For a = 0 the second family's
  first form steps into the first family.) From a(1) = 1, a(10+6k) = [1][3][(84)^(k+1)] for all k.
- Every start below 11^7 = 19487171 reaches one of the families, within at most 29 steps (the slowest is 16206883; output
  [`certificate/scan_11e7.txt`](certificate/scan_11e7.txt)).
- Open: that every start reaches a family.

**Argument.** Each step adds a digit string to its digit-wise inverse (1<->1, 3<->4, 5<->9, 7<->8, 2<->6); in
these forms the carries come only from 8+7 = 15 and 9+5 = 14 (and the leading 9+5 or 7+8), each moves one place,
and the result is again of the listed shape. In values: with R_a = (11^a - 1)/10 and P_b = (121^b - 1)/120 the
digit strings have closed forms d R_a and 92 P_b ((84)^b) or 80 P_b ((73)^b), and each step is a polynomial
identity in 11^a, 121^b.

**Evidence.**
- Lean (Mathlib): [`A053697_mathlib.lean`](A053697_mathlib.lean). `step` is the OEIS map on `Nat.digits 11`;
  `famI_1` ... `famI_6`, `famII_1` ... `famII_6` (each step, all a, b), `famI_cycle`, `famII_cycle` (step^6),
  `A053697_one_orbit` (the entry's example). `tools/leancheck-mathlib.sh`: OK, no warnings; axioms propext,
  Classical.choice, Quot.sound; no sorry, no native_decide.
- [`certificate/scan.py`](certificate/scan.py) with [`certificate/sim.py`](certificate/sim.py): all starts
  below 11^7.
- Outside Lean: the global convergence (open). Not verified in Lean: the scan below 11^7 (Python).

**Review level.** `lean-proof` for the family statements.

**Prior art.** Checked 2026-11-07. The entry has R. Israel's closed forms for the orbit of 1 (2016), which our
`A053697_one_orbit` re-proves; no proof of the family structure or of convergence found. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones, 2026-11-06).
