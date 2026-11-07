# OEIS A084742: a(8) = 0, so "no entry is zero" is false

**Source.** OEIS [A084742](https://oeis.org/A084742): least k such that (n^k+1)/(n+1) is prime, or 0 if
no such prime exists (offset 2). Old comment (Murthy, Srikanth 2003): "Conjecture: No entry is zero."
The name gained "or 0 if no such prime exists" when Eric Chen added a(8) = a(27) = a(32) = a(64) = 0
(Nov 2014; Dubner and Granlund, J. Integer Seq. 3 (2000), note that perfect powers usually give
composites).

**Result.** False: (8^k + 1)/9 is never a prime integer, so a(8) = 0.

**Argument.** Put u = 2^k, so 8^k + 1 = u^3 + 1. If 9 | u^3 + 1 then u = 3t + 2 and
(u^3 + 1)/9 = (t + 1)(3t^2 + 3t + 1). A prime product forces t = 0, where the quotient is 1.

**Evidence.** Lean (Mathlib): [`A084742_mathlib.lean`](A084742_mathlib.lean), `A084742_main :
A084742 8 = 0` with `A084742` the entry's definition (n + 1 divides n^k + 1 and the quotient is prime;
`Nat.find`, else 0); `A084742_cube_key`, `A084742_eight`. Axioms propext, Classical.choice,
Quot.sound. Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Known: E. Chen, OEIS A084742 comments and edit discussion (Nov 2014), following
Dubner–Granlund (2000). Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs
(2026-11-07). First Lean proof here.
