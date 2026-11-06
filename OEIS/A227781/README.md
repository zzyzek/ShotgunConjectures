# OEIS A227781: a(n) = 4 iff 8 | n, a(n) = 3 iff n = 4 mod 8

Settled together with A227784; see [`../A227784/README.md`](../A227784/README.md). True as stated, and a(n) <= 2
for all other n. Lean: [`../A227784/A227784_mathlib.lean`](../A227784/A227784_mathlib.lean), theorem
`A227784.A227781_conjecture` (and `A227784.A227781_le_two`). Known: Ramaswamy-Siddaramu (2010) determine the
level of Z/nZ.
