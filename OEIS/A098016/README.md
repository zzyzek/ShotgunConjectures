# OEIS A098016: the mean of consecutive primes is never prime

**Source.** [A098016](https://oeis.org/A098016), comment: "Conjecture: (1/2)(prime(x+1) + prime(x)) is not prime
for all x." (OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial.

**Argument.** For x = 1 the mean is 5/2, not an integer. For x ≥ 2 the mean is an integer strictly between the
consecutive primes prime(x) and prime(x+1), so it is not prime.

**Evidence.**
- Lean (Mathlib): [`A098016_mathlib.lean`](A098016_mathlib.lean), `A098016_main`: for every x and every prime q, 2q ≠ p_x + p_(x+1) (`Nat.nth Nat.Prime`). Nothing outside Lean.
- `certificate/check.py` (all consecutive primes below 10^6).

**Review level.** `lean-proof` (Mathlib file above).
**Prior art.** Known: [A098016](https://oeis.org/A098016) already has R. Israel's 2019 comment giving this argument. Searched OEIS entry, references and history. Checked 2026-11-04.
