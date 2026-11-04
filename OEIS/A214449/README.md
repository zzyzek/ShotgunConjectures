# OEIS A214449: A214449 is not A118168 with two 1s deleted (first mismatch n = 188)

**Source.** OEIS [A214449](https://oeis.org/A214449): least m > 0 with n! ≤ m^m (offset 1).
Conjecture: "this sequence results from A118168 by deleting the first two 1s." (OEIS text,
CC BY-SA 4.0.) A118168(n) = the x minimizing |x^x - n!| (offset 0: 1, 1, 1, 2, 3, 3, ...).

**Reading.** Deleting the first two terms of A118168 aligns A214449(n) with A118168(n+1).

**Result.** False. A214449(188) = 159 but A118168(189) = 158. There are 24 mismatches for
n ≤ 1500 (188, 248, 271, 310, ...).

**Argument.** 158^158 < 188! ≤ 159^159, so A214449(188) = 159. 189! ≈ 208·158^158 lies between
158^158 and 159^159 ≈ 431·158^158 and is nearer to 158^158, so A118168(189) = 158 (x^x is
increasing, so the minimizer is a neighbour).

**Evidence.**
- [`A214449.lean`](A214449.lean): the inequalities and the nearness comparison with exact
  integers (`decide +kernel`). Outside Lean: monotonicity of x^x.
- `certificate/a214449.py`: exact comparison for n ≤ 1500 (alignment and all mismatches).
- Lean (Mathlib): [`A214449_mathlib.lean`](A214449_mathlib.lean), `A214449_main`: A214449(188) = 159 (`Nat.find`) and 158 is the unique x minimizing |x^x - 189!|; monotonicity of x^x is proved there. Nothing outside Lean.

**Review level.** `lean-proof` for the disproof (Mathlib file above).

**Prior art.** New. [OEIS A214449](https://oeis.org/A214449) (fetched 2026-11-04) still states the conjecture (no edits since 2012); [A118168](https://oeis.org/A118168) has no relevant comment; web search found nothing. Searched: entries, OEIS cross-reference search, edit history, web. The counterexample at n = 188 is worth an OEIS comment. (Prior-art review 2026-11-04.)
