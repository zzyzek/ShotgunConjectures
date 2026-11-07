# OEIS A083144: no entry is zero (same proof as A083143)

**Source.** OEIS [A083144](https://oeis.org/A083144): smallest k such that k·prime(n) is an
n-digit palindrome, or 0 if none; a(n) = A083143(n)/prime(n). Conjecture: "no entry is zero"
(OEIS text, CC BY-SA 4.0).

**Result.** No entry is zero: a(n) = 0 exactly when A083143(n) = 0, and A083143 has no zero
entry.

**Argument and evidence.** See [`../A083143/README.md`](../A083143/README.md): repunit
construction when ord_p(10) ≤ n/2, Dias da Silva–Hamidoune subset sums of the pair values
10^i + 10^{n−1−i} otherwise (n ≥ 460), computation for n ≤ 459. No Lean. Outside Lean: the
Dias da Silva–Hamidoune theorem, the Rosser–Schoenfeld bound for p_n, and the computations.

**Review level.** `rechecked`.

**Prior art.** As for A083143 (checked 2026-11-07).
