# OEIS A221564: a(3k+1) = 2k for the FO4C3 shuffle

**Source.** [A221564](https://oeis.org/A221564), the number of FO4C3 moves (flip the top four cards over as a
unit, then cut three cards from top to bottom) that restore a packet of n cards in order and orientation.
Comment: "Conjecture: a(3k+1) = 2k." (OEIS text, CC BY-SA 4.0, read 2026-11-06.)

**Result.** True (known): A. Howroyd (Apr 27 2020) added the cycle description and the formula
a(3n+1) = 2n, a(3n) = a(3n−1) = 2n(n−1) to the entry. Reproved here in Lean for a(3k+1).

**Argument.** Number positions 0..n−1 from the top. One move sends position 0 to 0 (flipped), positions
1, 2, 3 to n−1, n−2, n−3 (flipped) and p ≥ 4 to p − 3. For n = 3k+1 the positions ≡ 2 (mod 3) form one cycle of
length k with one flip, the positions ≡ 0, 1 (mod 3) (except 0) form one cycle of length 2k with two flips, and
the top card flips each move. So 2k moves restore everything, and the card at position 2 is back unflipped only
after a multiple of 2k moves.

**Evidence.**
- Lean (Mathlib, for `Function.iterate`): [`A221564_mathlib.lean`](A221564_mathlib.lean),
  `A221564.A221564_main` (k ≥ 1): `restored (3k+1) (2k)` and no 0 < j < 2k restores. Check
  `tools/leancheck-mathlib.sh`: OK, no warnings, axioms at most propext, Classical.choice, Quot.sound.
- [`certificate/simulate.py`](certificate/simulate.py): deck simulation for n = 4..30 matches the data, and the
  position map `mv` of the Lean file agrees with the deck move.
- Outside Lean: the translation of the card move into the position map (checked by the simulation).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: the entry carries Howroyd's formula and cycle description (2020) next to the
conjecture; not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones).
