# OEIS A102613: π(n)/(n − π(n)) → 0

**Source.** [A102613](https://oeis.org/A102613), comment: "Conjecture: The ratio Pi(x)/(n-Pi(x)) tends to 0 as n
tends to infinity. ... but unfortunately not proof." (OEIS text, CC BY-SA 4.0.)

**Result.** True; a direct consequence of π(n)/n → 0.

**Argument.** π(n)/(n − π(n)) = (π(n)/n)/(1 − π(n)/n), and π(n)/n → 0 (Chebyshev, or an elementary sieve:
the proportion of integers ≤ n coprime to the first k primes tends to ∏(1 − 1/p), which is arbitrarily small).

**Evidence.** `certificate/check.py` (values at n = 10..10^9). Lean (Mathlib):
[`A102613_mathlib.lean`](A102613_mathlib.lean), theorem `A102613_conjecture`: π(n)/(n − π(n)) → 0 in ℝ, from
Chebyshev's bound `Chebyshev.eventually_primeCounting_le`. Nothing outside Lean.

**Review level.** `lean-proof`.
**Prior art.** Known: immediate from pi(n)/n -> 0 (classical). [A102613](https://oeis.org/A102613) still has the conjecture. Searched OEIS entry, references and history. Checked 2026-11-04.
