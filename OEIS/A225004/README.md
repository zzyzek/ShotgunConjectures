# OEIS A225004: a(n) divides n²

**Source.** [A225004](https://oeis.org/A225004), a(n) = the largest multiple of n with fewer than twice as many
divisors as n. Comment: "Conjecture: a(n) is always a divisor of n^2." (OEIS text, CC BY-SA 4.0, read 2026-11-06.)

**Result.** True: every positive multiple m of n with τ(m) < 2τ(n) divides n², so in particular a(n) | n²
(and the maximum exists, at most n²).

**Argument.** Let n | m, m > 0, and suppose v_p(m) = f > 2e with e = v_p(n) for some prime p. Write
m = p^f m', n = p^e n' with p ∤ m', n'. Then n' | m', so τ(n') ≤ τ(m'), and
τ(m) = (f+1)τ(m') ≥ (2e+2)τ(n') = 2τ(n). Hence τ(m) < 2τ(n) forces v_p(m) ≤ 2v_p(n) for every p, i.e. m | n².

**Evidence.**
- Lean (Mathlib): [`A225004_mathlib.lean`](A225004_mathlib.lean), `A225004.A225004_main : 1 ≤ n → a n ∣ n^2`
  with `a n = sSup {m | n ∣ m ∧ τ m < 2 τ n}`; `dvd_sq_of_good` is the lemma above, `a_good` shows the
  supremum is attained. Check `tools/leancheck-mathlib.sh`: OK, no warnings, axioms propext, Classical.choice,
  Quot.sound.
- Outside Lean: nothing beyond reading the definition.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: entry still says "Conjecture"; not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs (local clones). The argument is immediate from multiplicativity of τ; no published
proof found.
