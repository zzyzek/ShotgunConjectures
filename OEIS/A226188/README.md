# OEIS A226188: a(n+1)/a(n) → exp(2/3) = 1.947734... (harmonic-number threshold)

**Source.** OEIS [A226188](https://oeis.org/A226188): least positive integer k with 1 + 1/2 + ... + 1/k > 2n/3.
Conjecture: "a(n+1)/a(n) converges to 1.94..." (OEIS text, CC BY-SA 4.0.) The entry adds "Conjecture
confirmed" with limit exp(2/3) = 1.947734... (J.-F. Alcover, 2013, from the expansion of the harmonic numbers).

**Result.** True: a(n+1)/a(n) → exp(2/3).

**Argument.** H_k - log k decreases to Euler's γ, and H_k < log k + γ + 1/(2k). With c = 2/3,
H_(a-1) ≤ c n < H_a for a = a(n), so log(a - 1) + γ < c n < log a + γ + 1/(2a). Hence
log a(n) = c n - γ + o(1), and a(n+1)/a(n) = exp(c + o(1)) → exp(c).

**Evidence.**
- `certificate/a226160.py` (mpmath): a(n) for n ≤ 40 (first terms match the entry) and
  a(40)/a(39) = 1.947734.. agreeing with exp(2/3) to 10 digits.
- Lean (Mathlib): [`A226188_mathlib.lean`](A226188_mathlib.lean), `A226188_main`: if a(n) is the least k with H_k > n·2/3 for every n, then a(n+1)/a(n) → exp(2/3) (`Filter.Tendsto`). Uses Mathlib's H_k - log k → γ and H_k ≤ 1 + log k. Outside Lean: none.

**Review level.** `lean-proof`: the result is proved in Lean + Mathlib.

**Depends on (Mathlib).** H_k - log k → γ with the bound H_k < log k + γ + 1/(2k) (Mathlib has the
Euler–Mascheroni limit; the explicit bound may need work).

**Prior art.** Confirmed in the entry by J.-F. Alcover (2013). Resolved by others.
