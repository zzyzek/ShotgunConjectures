# CFG F5: lim f_3(n)/n^(1/3), minimum diameter of n points in R^3 with minimum distance 1

**Source.** H. T. Croft, K. J. Falconer, R. K. Guy, *Unsolved Problems in Geometry*, Springer 1991,
section F5. f_d(n) is the least diameter of a set of n points in R^d with minimum mutual distance 1.
The book quotes Thue's planar result lim f_2(n)/n^(1/2) = 2^(1/2) 3^(1/4) pi^(-1/2) and says the
value of lim f_3(n)/n^(1/3) is unsolved, related to optimal ball-packing density.

**Result.** Known (immediate consequence of the Kepler conjecture, proved by Hales):

lim f_3(n)/n^(1/3) = (3 sqrt2 / pi)^(1/3) = (6/(sqrt2 pi))^(1/3) = 1.10533...

**Argument.** Write delta = sqrt2, the point density of the face-centred cubic (fcc) lattice with
minimum distance 1 (cubic cell of side sqrt2 holding 4 points). Kepler (Hales): every packing of
balls of radius 1/2 in R^3 has density at most pi/sqrt18 = delta * (pi/6).

*Upper bound.* Let c be the circumradius of the Voronoi cell of the fcc lattice. The Voronoi cells
of the lattice points in the closed ball B(0, R) cover B(0, R - c), so B(0, R) holds at least
delta (4 pi/3)(R - c)^3 lattice points. Any n of them form a set with minimum distance 1 and
diameter at most 2R. Taking the least R with delta (4 pi/3)(R - c)^3 >= n gives
f_3(n) <= (6n/(delta pi))^(1/3) + O(1).

*Lower bound.* Let P be n points with minimum distance 1 and diameter D, K its convex hull
(diameter D). Fix s > 0 and cut R^3 into cubes of side s.
- A single cube Q: the balls of radius 1/2 around P cap Q lie in a cube of side s + 1. Repeating
  that cube periodically with period s + 1 gives a packing of density
  |P cap Q| (pi/6) / (s + 1)^3, so Kepler gives |P cap Q| <= delta (s + 1)^3.
- Cubes that meet K lie in K + B(0, s sqrt3), a set of diameter at most D + 2 sqrt3 s. By the
  isodiametric inequality its volume is at most pi (D + 2 sqrt3 s)^3 / 6, so at most that
  volume divided by s^3 cubes meet K.
Hence n <= delta (pi/6) (1 + 1/s)^3 (D + 2 sqrt3 s)^3. With s = sqrt D this is
n <= delta (pi/6) D^3 (1 + O(D^(-1/2))), so f_3(n) >= (6n/(delta pi))^(1/3) (1 - o(1)).

Both bounds give the limit (6/(sqrt2 pi))^(1/3). The same argument in the plane, with Thue's
hexagonal density 2/sqrt3, reproduces the book's planar constant 2^(1/2) 3^(1/4) pi^(-1/2).

**Evidence.**
- `certificate/fcc_ball.py`: fcc points in balls of radius 2, 4, 8, 16 give n = 55, 381, 3055,
  24307 and D/n^(1/3) = 1.052, 1.1035, 1.1027, 1.1047 (limit 1.10534).
- Lean status `needs-mathlib`, not attempted: the argument rests on the Kepler theorem (formalised
  in HOL Light and Isabelle by the Flyspeck project, not in Lean/Mathlib) and the isodiametric
  inequality (not in Mathlib).
- Outside Lean: the whole argument (Kepler theorem, isodiametric inequality, the cube averaging
  and the lattice point count above).

**Review level.** `rechecked` (argument re-derived by hand; numerical check of the construction).

**Prior art.** Checked 2026-11-06.
- T. Hales, *A proof of the Kepler conjecture*, Ann. of Math. 162 (2005) 1065-1185; T. Hales et
  al., *A formal proof of the Kepler conjecture*, Forum Math. Pi 5 (2017) e2.
- The book itself ties the question to optimal packing densities; once Kepler is known the limit
  follows by the standard finite-to-infinite density argument above. Web searches did not locate a
  paper stating the n^(1/3) constant explicitly; we record it as a routine corollary.
- google-deepmind/formal-conjectures tree HEAD 2026-11-06: no Kepler or minimum-diameter file.
