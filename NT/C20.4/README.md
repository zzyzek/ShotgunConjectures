# Guy C20/D3: three hexagonal (pentagonal) numbers of positive rank

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, section D3 (cross-referenced from C20). Paraphrased: is every sufficiently large number a sum of three hexagonal numbers r(2r−1), r > 0 (equivalently 8k+3 a sum of three squares of positive numbers 4r−1)? Same for pentagonal numbers r(3r−1)/2, r > 0 (24k+3 as three squares of positive numbers 6r−1).

**Result.** Hexagonal: yes, known (Duke–Schulze-Pillot 1990, ineffective bound). Pentagonal: open; Z.-W. Sun conjectured (2019) that every n > 33066 is such a sum; no proof found.

**Argument.** Hexagonal: 8n + 3 = x² + y² + z² with x, y, z ≡ 3 (mod 4) and x, y, z > 0. Duke and Schulze-Pillot prove that representations of large integers by a positive ternary form, with congruence conditions, are equidistributed on the ellipsoid, so some lie in the positive octant; they state the hexagonal application. The same route for pentagonal numbers needs the classes x ≡ 5 (mod 6) together with positivity; we found no source that carries it out.

**Evidence.** `certificate/exceptions.py` (`exceptions.out`): up to 10⁶ the numbers that are not a sum of three positive-rank hexagonal numbers number 774 with largest 146858 (McCranie's last term in OEIS A007536), and for pentagonal numbers 283 with largest 33066 (Blecksmith–Selfridge, Sun). Lean: none (the theorem rests on modular forms; nothing finite settles "sufficiently large").

**Review level.** `agent` for the citation (theorem text not read; attribution seen in OEIS and secondary sources); `rechecked` for the tables.

**Prior art.** W. Duke, R. Schulze-Pillot, Representation of integers by positive ternary quadratic forms and equidistribution of lattice points on ellipsoids, Invent. Math. 99 (1990) 49–57 (hexagonal case). OEIS A007536. Pentagonal: Z.-W. Sun's conjecture, cited in D. Krachun, Z.-W. Sun, On sums of four pentagonal numbers with coefficients, [arXiv:2001.05325](https://arxiv.org/abs/2001.05325). Searched web, arXiv, OEIS, formal-conjectures (no entry), 2026-11-06.
