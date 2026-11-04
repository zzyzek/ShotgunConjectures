# OEIS A226160: a(n+1)/a(n) → exp(1/φ) = 1.855276958... (harmonic-number threshold)

**Source.** OEIS [A226160](https://oeis.org/A226160): least positive integer k with 1 + 1/2 + ... + 1/k > n/φ, φ the golden ratio.
Conjecture: "a(n+1)/a(n) converges to 1.8552..." (OEIS text, CC BY-SA 4.0.) The entry adds "Conjecture
confirmed" with limit exp(1/φ) = 1.855276958... (J.-F. Alcover, 2013, from the expansion of the harmonic numbers).

**Result.** True: a(n+1)/a(n) → exp(1/φ).

**Argument.** H_k - log k decreases to Euler's γ, and H_k < log k + γ + 1/(2k). With c = 1/φ,
H_(a-1) ≤ c n < H_a for a = a(n), so log(a - 1) + γ < c n < log a + γ + 1/(2a). Hence
log a(n) = c n - γ + o(1), and a(n+1)/a(n) = exp(c + o(1)) → exp(c).

**Evidence.**
- `certificate/a226160.py` (mpmath): a(n) for n ≤ 40 (first terms match the entry) and
  a(40)/a(39) = 1.85527695 agreeing with exp(1/φ) to 10 digits.
- Lean (Mathlib): [`A226160_mathlib.lean`](A226160_mathlib.lean), `A226160_main`: if a(n) is the least k with H_k > n·1/φ for every n, then a(n+1)/a(n) → exp(1/φ) (`Filter.Tendsto`). Uses Mathlib's H_k - log k → γ and H_k ≤ 1 + log k. Outside Lean: none.

**Review level.** `lean-proof`: the result is proved in Lean + Mathlib.

**Depends on (Mathlib).** H_k - log k → γ with the bound H_k < log k + γ + 1/(2k) (Mathlib has the
Euler–Mascheroni limit; the explicit bound may need work).

**Prior art.** Confirmed in the entry by J.-F. Alcover (2013). Resolved by others.
