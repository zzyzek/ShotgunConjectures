# OEIS A051451: the "next twin pair above a(n)" form fails at n = 35

**Source.** OEIS wiki Talk:Conjectures/List, entry for [A051451](https://oeis.org/A051451) (line 154), by
M. Winkler (2013): "Conjecture: For every n > 2, there exists a twin prime pair [p, p+2] with p < a(n) such
that the "next" twin prime pair > a(n) is [a(n)+p, a(n)+p+2]." (OEIS text, CC BY-SA 4.0.)
a(n) = lcm(1..x), x the n-th prime power (A000961, starting at 1).

**Reading.** The current entry (checked 2026-11-01) words the conjecture without "next": some twin pair
[p, p+2] with p < a(n) has [a(n)+p, a(n)+p+2] also a twin pair (verified there for n ≤ 1000). That version
is not addressed here and stays open. This item concerns the 2013 "next" version.

**Result.** The "next" version is false at n = 35.

**Argument.** A000961(35) = 89, so L = a(35) = lcm(1..89) (39 digits). The first twin prime pair above L
is [L + 17159, L + 17161], and 17161 = 131^2 is not prime, so the offset 17159 is not the smaller member of
a twin prime pair. (Every offset m < 89^2 coprime to all primes ≤ 89 is prime, but the first twin pair
typically lies near 0.76·x^2 = 6000 or more here, so composite offsets occur.)

**Evidence.**
- Lean (Mathlib): [`A051451_mathlib.lean`](A051451_mathlib.lean) proves the full result (`A051451_false, index_35`): with L = lcm(1..89) = a(35): no twin pair in (L, L+17159), L+17159 and L+17161 prime (Pratt certificates, 39 digits), so the next twin pair is at offset 17159 and no p as in the conjecture exists (17161 = 131^2); index_35 checks A000961(35) = 89. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`A051451.lean`](A051451.lean) (`decide +kernel`): L = lcm(1..89); for every 1 ≤ m < 17159,
  L + m or L + m + 2 has an explicit divisor strictly between 1 and itself (2, a prime ≤ 89, or one of 309
  divisors found with PARI), so no twin pair has offset < 17159; 17161 = 131·131.
  Outside Lean: primality of L + 17159 and L + 17161 (PARI `isprime`, APR-CL), which places the first pair
  at offset 17159.
- `certificate/a051451.gp` (search over n), `a051451_verify.gp` (the n = 35 certificate),
  `a051451_divisors.gp` (the 309 divisors used in Lean).

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`A051451_mathlib.lean`](A051451_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`A051451.lean`](A051451.lean) checks the parts named under Evidence.
**Prior art.** New: no source gives the n = 35 failure of the "next twin pair" wording. That wording is no longer in [A051451](https://oeis.org/A051451); the current conjecture (without "next", verified for n <= 1000 by M. Winkler, 2026) is not addressed. Searched OEIS entry, references and history, web. Checked 2026-11-04.
