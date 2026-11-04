# OEIS A121627: divisibility of the "complex factorial" real parts

**Source.** [A121627](https://oeis.org/A121627) (a(n) = Re(∏_{k≤n} k(1+i))), comment: "Conjecture (1): Current nonzero
term divides next nonzero term ... Conjecture (2): If the term in (12, 8, 5, ...) is generated from a(n)/a(n-1) or
a(n)/a(n-2), then n divides each (12, 8, 5, ...)." (OEIS text, CC BY-SA 4.0.)

**Result.** True. Derived in the entry from explicit formulas (H. Fischer, 2011); re-derived here.

**Argument.** a(n) = n!·Re((1+i)^n) = n!·2^(n/2)·cos(nπ/4). It vanishes iff n ≡ 2, 6 (mod 8), and otherwise
|a(n)| = n!·2^⌊n/2⌋. For consecutive nonzero indices m < n (n − m ∈ {1, 2}), a(n)/a(m) = ±(n!/m!)·2^(⌊n/2⌋−⌊m/2⌋),
an integer divisible by n.

**Evidence.** `certificate/check.py`: n ≤ 400 (exact Gaussian-integer recursion). No Lean file.

**Review level.** `rechecked`.
**Prior art.** H. Fischer, comments in A121627 (checked 2026-11-01). Resolved by others.
