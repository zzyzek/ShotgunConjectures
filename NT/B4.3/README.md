# Guy UPINT B4: the smallest odd amicable pair coprime to 3

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section B4 (paraphrased): Bratley and McKay
conjectured that both members of every odd amicable pair are divisible by 3; Battiato and Borho found
counterexamples, and te Riele announced (1987) a 33-digit one. Guy asks: is that the smallest such pair? Is there an
odd pair with exactly one member divisible by 3? Is there a pair whose members have different smallest prime factors?

**Result.** First question answered (known): no. The 32-digit pair
m = 42262694537514864075544955198125 = 5⁴·7²·11²·13²·19³·29·37·71·109·181·347·2833·6659,
n = 42405817271188606697466971841875 = 5⁴·7²·11²·13²·19³·29·37·71·109·181·6568305119
is amicable, odd and coprime to 3 (in J. M. Pedersen's lists; MathWorld "Amicable Pair" calls it the smallest known
pair not divisible by 6). Whether it is the smallest such pair, and the second and third questions, remain open.

**Argument.** σ is multiplicative. With A = 5⁴·7²·11²·13²·19³·29·37·71·109·181, σ(A) = 12890465692724011392000,
and σ(m) = σ(A)·348·2834·6660 = m + n = σ(A)·6568305120 = σ(n).

**Evidence.**
- Lean (Mathlib): [`B4_3_mathlib.lean`](B4_3_mathlib.lean), namespace `NT_B4_3`. Main theorem
  `odd_amicable_coprime3_32digits`: σ₁ m = σ₁ n = m + n (Mathlib's `ArithmeticFunction.sigma 1`), m ≠ n, both odd,
  3 ∤ m, 3 ∤ n, both < 10^32. Primality of 6568305119 by a Pratt certificate (`OpenProblemsLib.Pratt`).
  Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext, Classical.choice, Quot.sound.
- [`certificate/check.gp`](certificate/check.gp): factorizations and σ in PARI/gp.
- Outside Lean: the size of te Riele's pair (33 digits, from Guy's text); minimality of the 32-digit pair (open).

**Review level.** `lean-proof` for the example.

**Prior art.** Checked 2026-11-06: MathWorld "Amicable Pair" (citing Pedersen); Battiato-Borho, Math. Comp. 50
(1988); formal-conjectures has `Wikipedia/AmicableNumbers.lean` (coprime pairs, opposite parity, infinitude; open)
but nothing on pairs coprime to 3.
