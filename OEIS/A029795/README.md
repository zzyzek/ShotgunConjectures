# OEIS A029795: k and k^3 with the same digits are not eventually all integers

**Source.** [A029795](https://oeis.org/A029795), comment by C. R. Greathouse IV (2011): "Conjecture: there
exists some m and N for which a(n) = m + n for all n >= N." (OEIS text, CC BY-SA 4.0.)

**Result.** False.

**Argument.** If a(n) = m + n for n ≥ N, every integer ≥ a(N) is a term. But for e ≥ 1, 10^e + 1 has
digits {0, 1} while (10^e + 1)^3 = 10^(3e) + 3·10^(2e) + 3·10^e + 1 has the digit 3 at position e. So
there are non-terms beyond every bound. (The same idea as M. Corneth's remark on A029797.)

**Evidence.**
- Lean: [`A029795.lean`](A029795.lean) proves `main`: no M has every x ≥ M with the same digit set as
  x^3. Axioms: propext, Classical.choice, Quot.sound.
- Lean + Mathlib: [`A029795_mathlib.lean`](A029795_mathlib.lean), `A029795_main`: with a = `Nat.nth` of
  "same `Nat.digits 10` set as the cube", there are no m : ℤ, N with a(n) = m + n for all n ≥ N.
  Outside Lean: nothing.

**Review level.** `lean-proof`: the conjecture as stated about a(n), in [`A029795_mathlib.lean`](A029795_mathlib.lean).
**Prior art.** Partly known. The same conjecture in [A029797](https://oeis.org/A029797) was refuted by D. A. Corneth (2023) with 10^e + 1, the argument used here; [A029795](https://oeis.org/A029795) still has it open. Searched OEIS entries, references and history, web. Checked 2026-11-04.
