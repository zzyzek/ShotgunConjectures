# OEIS A195507: the recurrence a(n+1) = d a(n) - (d-1) n + 1

**Source.** OEIS [A195507](https://oeis.org/A195507): a(n) = smallest m > n with m ≡ n (mod k)
for k = 1..n-1. Conjecture: "Write a(n)/n in lowest terms as num/d. Then a(n+1) = d*a(n) -
(d-1)*n + 1." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** m ≡ n (mod k) for all k < n iff L = lcm(1..n-1) divides m - n, so a(n) = n + L
(Adams-Watters, in the entry). The reduced denominator of (n + L)/n is
d = n/gcd(n + L, n) = n/gcd(L, n). Then lcm(1..n) = lcm(L, n) = L n/gcd(L, n) = d L, so
a(n+1) = n + 1 + d L = d(n + L) - (d - 1)n + 1.

**Evidence.**
- [`A195507.lean`](A195507.lean): `recurrence`, for all n ≥ 1 and all L:
  (n+1) + lcm(L, n) = d (n+L) - (d-1) n + 1 with d = n / gcd(n+L, n) (core Lean); `small`:
  a(n) = n + lcm(1..n-1) by brute force for n ≤ 9. Outside Lean: the one-line identification
  a(n) = n + lcm(1..n-1) for general n.
- `certificate/a195507.py`: brute force for n ≤ 14, recurrence for n < 400.
- Lean (Mathlib): [`A195507_mathlib.lean`](A195507_mathlib.lean), `A195507_main`: with a(n) = least m > n with m ≡ n (mod k) for 1 ≤ k ≤ n-1 (`Nat.find`) and d = `Rat.den` of a(n)/n, a(n+1) = d·a(n) - (d-1)·n + 1 for every n ≥ 1; `A195507_eq`: a(n) = n + lcm(1..n-1). Nothing outside Lean.

**Review level.** `lean-proof` (Mathlib file above).

**Prior art.** Known. [OEIS A195507](https://oeis.org/A195507) (fetched 2026-11-04) already proves it (Adams-Watters, 2011: a(n) = n + A003418(n-1)). Searched: entry, OEIS cross-reference search. (Prior-art review 2026-11-04.)
