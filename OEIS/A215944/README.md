# OEIS A215944: Coman's 5461(42k − 13) exception claim is false (counterexample 3048841)

**Source.** [A215944](https://oeis.org/A215944) (Fermat pseudoprimes to base 2 with three prime factors divisible by a
smaller base-2 pseudoprime). Comment by Marius Coman (Aug 2012): "Conjecture: The only Fermat pseudoprimes to base 2
divisible by a smaller Fermat pseudoprime to base 2 that can't be written as p*((m + 1)*p - m)*((n + 1)*p - n), where
m, n, p are natural numbers, are multiples of 5461 and can be written as 5461*(42*k - 13)." Checked there for the 30
listed terms (up to 2299081) and the first 15 such numbers with four prime factors. (OEIS text, CC BY-SA 4.0; no
counterexample in the entry, revision #23, Dec 2025, checked 2026-11-06.)

**Reading.** The claim is refuted under the broadest reading: p ≥ 1 any natural number (not only a prime factor),
m, n ≥ 0. A counterexample under it is a counterexample under every narrower reading.

**Result.** False. P = 3048841 = 61 · 151 · 331 is a base-2 Fermat pseudoprime, divisible by the smaller base-2
pseudoprime 49981 = 151 · 331, not divisible by 5461, and not of the form p((m+1)p − m)((n+1)p − n) for any natural
p, m, n. It is the least counterexample (it is a(36) of A215944, just past the terms Coman checked). Below 10¹³ there
are 56782 base-2 pseudoprimes divisible by a smaller one; 4042 of them fail the strict reading (p a prime factor,
m, n ≥ 1) without being 5461(42k − 13), and 4019 fail even the broad reading.

**Argument.** (m+1)p − m = p + m(p − 1), so P = p·A·B with A ≡ B ≡ p (mod p − 1) and A, B ≥ p. p, A, B divide P,
so they are among its 8 divisors; none of the triples with product P satisfies the congruences (checked
exhaustively). p = 0, 1 give 0 and 1.

**Evidence.**
- Lean (Mathlib + lib): [`A215944_mathlib.lean`](A215944_mathlib.lean), main `A215944_counterexample`: FermatPsp
  3048841 2 ∧ (∃ d, FermatPsp d 2 ∧ d ∣ 3048841 ∧ d < 3048841) ∧ ¬ 5461 ∣ 3048841 ∧ ∀ p m n : ℕ,
  p*((m+1)*p − m)*((n+1)*p − n) ≠ 3048841. Uses lib `pspCheck` (kernel powMod) and `divisorsList`; `decide +kernel`.
  Check `tools/leancheck-mathlib.sh`: exit 0, no warnings; axioms propext, Classical.choice, Quot.sound; no
  `native_decide`.
- [`certificate/search.py`](certificate/search.py) over the Feitsma–Galway list below 10¹³ (data/, see DATA.md;
  4 s); output [`certificate/search.log`](certificate/search.log).
- Outside Lean: minimality and the counts (Python over the published table).

**Review level.** `lean-witness` (the counterexample settles the claim; the Lean file proves it completely).

**Prior art.** Checked 2026-11-06: entry, b-file (3048841 = a(36)), web search; no counterexample found. Not in
google-deepmind/formal-conjectures (clone 2026-11-05) or otoi-lab/oeis-lean-proofs (clone 2026-10-13).
