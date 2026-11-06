# OEIS A132293: maximal number of right angles in an n-gon (Mathar's correction)

**Source.** [A132293](https://oeis.org/A132293), "Maximal number of right angles in an n-gon", offset 3, data
1, 4, 3, 4, 5, 6, with the editors' note "A proper definition is needed for this sequence". Conjecture (R. J. Mathar,
Mar 07 and Apr 21 2008, in the entry): the correct sequence is a(n) = A014681(n-1), because a zigzag staircase
polyomino has as many right angles as edges. M. Paulovic (Sep 27 2023): possibly an incorrect version of
[A049008](https://oeis.org/A049008). (OEIS text, checked 2026-11-06.)

**Reading.** The entry does not say whether reflex 270° angles count as right angles. A014681(n-1) is n for even n
and n - 2 for odd n (n >= 3). Mathar's staircase counts every corner of a rectilinear polygon, so his reading is:
simple polygon, no straight (180°) vertices, an interior angle is "right" if it is 90° or 270°. A049008 is the other
reading (only 90° counts).

**Result.** The entry is misstated: its data match neither reading (a(6) = 4 is too small under both: an L-shaped
hexagon has six 90°/270° corners, and A049008(6) = 5). Under Mathar's reading his conjecture is true: the maximum is
n for even n >= 4 and n - 2 for odd n >= 3. Under the 90°-only reading the answer is A049008 (from n = 6 on,
A004396), a separate known sequence.

**Argument** (Mathar's reading).
1. Upper bound for odd n. The interior angles sum to (n-2)·180°. If n - 1 of them are 90° or 270°, their sum is
   (n-1)·90° = 0 (mod 180°) since n - 1 is even, so the last angle is 0 (mod 180°), hence 180° (excluded) or, if all n
   are right, the total is n·90° = 90° (mod 180°), which is not 0 (mod 180°). So at most n - 2.
2. Even n >= 4: the rectangle (n = 4) and staircase polygons (each extra step adds two corners) are rectilinear with
   n corners, all 90° or 270°.
3. Odd n: n = 3, a right triangle; n >= 5, cut one convex corner of a rectilinear (n-1)-gon by a short segment at 45°,
   which replaces one 90° corner by two 135° corners: n vertices, n - 2 right angles.

**Evidence.** Paper argument only; `lean_status: none` (Euclidean polygon angle sums are not formalised here). The
whole argument is outside Lean.

**Review level.** `agent`.

**Prior art.** Checked 2026-11-06: A132293, A014681, A049008, A004396 entries; google-deepmind/formal-conjectures
and otoi-lab/oeis-lean-proofs (no entries). The parity bound is folklore for rectilinear polygons (they have an even
number of vertices); the 90°-only maximum is A049008.
