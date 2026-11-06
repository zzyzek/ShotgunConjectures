# OEIS A005376: a(n) is approximately c*n, c the real root of x^5 + x - 1

**Source.** [A005376](https://oeis.org/A005376), a(n) = n - a(a(a(a(a(n-1))))), a(0) = 0. Comment by Benoit
Cloitre (Nov 05 2002): "Conjecture: a(n) is approximately c*n, where c is the real root of x^5+x-1 = 0,
c=0.754877666...". (OEIS text, CC BY-SA 4.0, revision #68, checked 2026-11-06.)

**Reading.** "Approximately c*n" read as a(n)/n -> c.

**Result.** True, and known: a(n) = c*n + O(log n) (stronger than the conjecture).

**Argument (known, summarised).** Let L(i) = L(i-1) + L(i-5) (A003520, 1, 2, 3, 4, 5, 6, 8, 11, ...). Every n
has a unique greedy representation as a sum of L(i) with indices at least 5 apart, and a(n) is obtained by
replacing each L(i) with L(i-1) (the "Lamé antecedent" rule in the entry; Meek-van Rees type numeration
theorem for generalised Hofstadter functions). The characteristic polynomial factors as
x^5 - x^4 - 1 = (x^3 - x - 1)(x^2 - x + 1); its dominant root is the plastic number rho = 1.3247..., and
c = 1/rho satisfies c^5 + c - 1 = 0. Then L(i-1) - c L(i) is a combination of powers of the other roots, two
of modulus < 1 and two of modulus 1, so each digit contributes O(1) error and a(n) - c n = O(number of
digits) = O(log n). Proofs: K. Dilcher, "On a class of iterative recurrence relations", Applications of
Fibonacci Numbers 5 (1993) 143-158; P. Letouzey, arXiv:2502.12615 (2025), which states that almost all of
the article is formalised in Coq/Rocq. The entry's own comment (P. Letouzey, Mar 06 2025) records
a(n) = c*n + O(ln n).

**Evidence.**
- [`certificate/check.py`](certificate/check.py) ([`check.out`](certificate/check.out)): a(n) for n <= 2*10^6;
  max |a(n) - c n| on [2^(k-1), 2^k] grows slowly (3.24 on [2^19, 2^20]), consistent with O(log n).
- Lean: none. A Lean proof would need the numeration theorem for L(i) (existence, uniqueness, and that the
  shift satisfies the nested recurrence) plus the root-modulus estimate; not attempted within this round.
- Outside Lean: everything (cited theorem; Coq/Rocq formalisation by Letouzey per arXiv:2502.12615).

**Review level.** `rechecked` (numerical check of the cited statement; proof not re-derived in full).

**Prior art.** Checked 2026-11-06: OEIS entry (Letouzey comment, Dilcher 1993, arXiv:2502.12615,
arXiv:2410.00529); not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
