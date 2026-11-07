# OEIS A085574: n(n+1)(n+2) + k palindromic needs k >= 2 for 108 < n < 4.6e12 (partial; conjecture open)

**Source.** [A085574](https://oeis.org/A085574) (Jason Earls, Jul 06 2003): least k such that n(n+1)(n+2) + k is a
palindrome. "Conjecture: For all n > 108, a(n) is > 1." (OEIS text, CC BY-SA 4.0, checked 2026-11-07.)

**Reading.** a(n) <= 1 iff f0(m) = m^3 - m or f1(m) = m^3 - m + 1 is a palindrome, m = n + 1.

**Result.** Partial: the conjecture holds for 108 < n < 4.6e12. All palindromic values of f0 and f1 below 10^38 are
6, 7, 121, 505, 74047, 474474, 1190911, 1294921 (n = 1, 1, 4, 7, 41, 77, 105, 108). Open beyond.

**Method.** For a D-digit palindrome P = f_e(m), the lowest j digits of P are the top j digits reversed. The lowest
j digits depend only on m mod 10^j, and the top j digits confine m to an interval of length about 10^(D/3 - j)/3.
For each residue of m mod 10^j (j = floor(D/6)) the program enumerates the candidates in that interval and checks
them exactly in 128-bit arithmetic: about 2 10^(D/6) work per length D, D <= 38 (P < 10^38, n < 4.6e12).

**Evidence.**
- [`certificate/mitm.c`](certificate/mitm.c) (`./mitm 1 38`, 7 s): the 8 solutions above, none for D >= 8.
- [`certificate/search.c`](certificate/search.c): direct enumeration n <= 1e9, same 8 solutions (cross-check).
- [`certificate/family.py`](certificate/family.py): no carry-free two-block family m = a 10^k +- b (a, b < 400) gives
  palindromes for all large k, so no infinite family of that shape refutes the conjecture.
- Outside Lean: all of it (C and Python computations). lean_status none.

**Review level.** `rechecked` (two independent searches agree up to 1e9).

**Prior art.** Checked 2026-11-07: entry data only (no b-file); Erich Friedman's "Palindromic Problem #2" (linked
in the entry) is the source. Heuristically the expected number of further solutions is about sum m^(-3/2), so the
conjecture is very likely true; a proof would need a finiteness theorem for palindromic values of a cubic, which is
not available (obstruction analysis: `open-problems/work/OEIS-A085574/REPORT.md`).
