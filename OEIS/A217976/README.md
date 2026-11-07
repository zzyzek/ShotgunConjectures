# OEIS A217976: the last v in A217865 comes before the first v+2

**Source.** [A217976](https://oeis.org/A217976), first time n appears in A217865 (first differences of
floor(n log n)). Comment: "Conjecture: the last time n appears is always before the first time n+2
appears." The same conjecture is stated in [A217866](https://oeis.org/A217866).

**Result.** True. Proof, Lean file and certificate are in [`../A217866/`](../A217866/README.md):
every occurrence of v in A217865 precedes every occurrence of v + 2, because
(n+1) log(n+1) - n log n is strictly increasing and each difference of floors is within 1 of it.

**Review level.** `lean-proof` (theorem `A217866_conjecture` in `../A217866/A217866_mathlib.lean`).

**Prior art.** As for A217866 (checked 2026-11-07).
