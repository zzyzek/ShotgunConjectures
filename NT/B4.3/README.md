# Guy UPINT B4: the smallest odd amicable pair coprime to 3

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., section B4 (paraphrased): Bratley and McKay
conjectured that both members of every odd amicable pair are divisible by 3; Battiato and Borho found
counterexamples, and te Riele announced (1987) a 33-digit one. Guy asks: is that the smallest such pair? Is there an
odd pair with exactly one member divisible by 3? Is there a pair whose members have different smallest prime factors?

**Result.** All three questions answered (known pairs; minimality from a complete list).
1. Smallest odd pair coprime to 3: m = 5480828320492525 = 5^2·7^2·11·13·17·19·23·31·103·1319, n = 5786392931193875 = 5^3·7·11·13·19·31·37·43·61·809 (16 digits). It is the smallest because S. Chernykh's amicable-pair list (sech.me/ap) is complete below 10^20 and contains no smaller odd pair coprime to 3.
2. Odd pair with exactly one member divisible by 3: 445953248528881275 = 3^2·5^2·7·13·19·37·43·73·439·22483 and 659008669204392325 = 5^2·7·13·19·37·73·571·1693·5839, the smallest such pair by the same list.
3. Members with different smallest prime factors: the pair in 2 (3 and 5).
The 32-digit pair m = 42262694537514864075544955198125, n = 42405817271188606697466971841875 recorded on 2026-11-06 (Pedersen's lists, MathWorld) is also odd and coprime to 3, but it is not the smallest; that earlier write-up was wrong to call minimality open and to call questions 2 and 3 open. Corrected 2026-11-07 (round r22, NT-B4.4 data).

**Argument.** σ is multiplicative. With A = 5⁴·7²·11²·13²·19³·29·37·71·109·181, σ(A) = 12890465692724011392000,
and σ(m) = σ(A)·348·2834·6660 = m + n = σ(A)·6568305120 = σ(n).

**Evidence.**
- Lean (Mathlib): [`B4_3_mathlib.lean`](B4_3_mathlib.lean), namespace `NT_B4_3`. Main theorem
  `odd_amicable_coprime3_32digits`: σ₁ m = σ₁ n = m + n (Mathlib's `ArithmeticFunction.sigma 1`), m ≠ n, both odd,
  3 ∤ m, 3 ∤ n, both < 10^32. Primality of 6568305119 by a Pratt certificate (`OpenProblemsLib.Pratt`).
  Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms at most propext, Classical.choice, Quot.sound.
- [`certificate/check.gp`](certificate/check.gp): factorizations and σ in PARI/gp.
- Lean covers the 32-digit example only. The 16-digit and 18-digit pairs are checked in PARI/gp (sigma(m) = sigma(n) = m + n, residues mod 3; gp -q -D recover=0, exit 0) and listed in ~/claude/open-problems/work/NT-B4.4/b43-side-finding.txt.
- Outside Lean: the 16- and 18-digit pairs (PARI check) and their minimality (completeness of Chernykh's list below 10^20).

**Review level.** `lean-proof` for the example.

**Prior art.** Checked 2026-11-06: MathWorld "Amicable Pair" (citing Pedersen); Battiato-Borho, Math. Comp. 50
(1988); formal-conjectures has `Wikipedia/AmicableNumbers.lean` (coprime pairs, opposite parity, infinitude; open)
but nothing on pairs coprime to 3.
