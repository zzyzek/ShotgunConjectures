# OEIS A223925: a(2n) = 4^n divides A132049(2n)

**Source.** [A223925](https://oeis.org/A223925) (Paul Curtz, 2013): a(2n+1) = 2n-1, a(2n) = 4^n. Comment:
"Conjecture: a(2n) is always a divisor of A132049(2n)." [A132049](https://oeis.org/A132049): numerator of
2n A000111(n-1)/A000111(n) in lowest terms. (OEIS text, CC BY-SA 4.0, A223925 revision #37 of Jul 30 2018, A132049
revision #49 of Jun 28 2026, checked 2026-11-06.)

**Result.** True, and sharp: v_2(A132049(2n)) = 2n exactly for every n >= 1, so 4^n divides A132049(2n) and
A132049(2n)/4^n is odd.

**Argument.** A132049(2n) is the numerator of 4n T_n / E_n with T_n = A000111(2n-1) = A000182(n) (tangent number)
and E_n = A000111(2n) = A000364(n) (secant number).
1. E_n is odd (classical: E_n == 1 mod 2, from the secant series sec x = 1/cos x mod 2, or the Seidel triangle
   mod 2). So the gcd removed in lowest terms is odd and v_2(numerator) = v_2(4n T_n) = 2 + v_2(n) + v_2(T_n).
2. T_n = 2^{2n}(2^{2n}-1)|B_{2n}|/(2n) = 2^{2n-2} G_n / n with G_n = 2(2^{2n}-1)|B_{2n}| the Genocchi number
   A110501(n). By von Staudt-Clausen B_{2n} = A - sum_{(p-1) | 2n} 1/p with A an integer; for odd p in the sum,
   p | 2^{2n} - 1 (Fermat), and the p = 2 term contributes 2^{2n} - 1, which is odd. Hence G_n is an odd integer and
   v_2(T_n) = 2n - 2 - v_2(n).
3. So v_2(A132049(2n)) = 2 + v_2(n) + 2n - 2 - v_2(n) = 2n.
The ingredients (secant numbers odd, tangent-Bernoulli formula, von Staudt-Clausen, Genocchi numbers odd) are
classical; the conjecture is a direct consequence. Curtz's remark that the quotients begin like A110501 is the
Genocchi factor of step 2.

**Evidence.**
- [`certificate/check.py`](certificate/check.py): A000111 from the Seidel-Entringer triangle (the A132049 Maple
  program); for n <= 300, v_2(A132049(2n)) = 2n, E_n odd, v_2(T_n) = 2n - 2 - v_2(n); exit 0.
- Lean: none. Outside Lean: the whole argument. Mathlib has von Staudt-Clausen (`Bernoulli.vonStaudt_clausen`, used
  in `lib/OpenProblemsLib/BernoulliDen.lean`) but not the tangent and secant numbers or their relation to
  Bernoulli numbers.

**Review level.** `rechecked`.

**Prior art.** Checked 2026-11-06. Classical facts: tangent numbers T_n = 2^{2n}(2^{2n}-1)|B_{2n}|/(2n) and the
Genocchi numbers G_n = 2(2^{2n}-1)|B_{2n}| are odd integers (formulas in OEIS A000182 and
A110501). The entry still lists the divisibility as a conjecture. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
