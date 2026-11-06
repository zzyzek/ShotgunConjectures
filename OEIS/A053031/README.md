# OEIS A053031: m has one zero in the Fibonacci numbers mod m iff ...

Settled together with A053029; see [`../A053029/README.md`](../A053029/README.md). Lean theorem `A053031_conj` in
[`../A053029/A053029_mathlib.lean`](../A053029/A053029_mathlib.lean): for every m >= 1, one zero per Pisano period
iff m is odd with all prime factors having one zero, or m is 2 or 4 times such an odd number. Known (Benfield and
Lippard, Fibonacci Quart. 63 (2025) 240-258); reproved in Lean here.
