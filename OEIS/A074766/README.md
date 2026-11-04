# OEIS A074766: p(2n) − 2p(n) < 2n for all n

**Source.** [A074766](https://oeis.org/A074766) (a(n) = prime(2n) − 2·prime(n) − n), comment:
"Conjecture: p(2n)-2p(n) < 2n for all n." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Dusart (1999): p_k ≤ k(ln k + ln ln k − 0.9484) for k ≥ 39017 and
p_k ≥ k(ln k + ln ln k − 1) for k ≥ 2. For n ≥ 19509 (so 2n ≥ 39017):
p(2n) − 2p(n) ≤ 2n·(ln 2 + 0.0516 + ln(ln 2n / ln n)) = 2n·(ln 2 + 0.0516 + ln(1 + ln 2/ln n)).
The bracket decreases in n and equals 0.8126 at n = 19509, so p(2n) − 2p(n) < 0.82·2n < 2n.
For n < 19509 the inequality is checked directly.

**Evidence.**
- `certificate/check.py`: direct check for n < 10^6 and the value of the bound at n = 19509.
  (The scan's `checks.gp` checked n ≤ 2·10^6.)
- Lean: needs Mathlib and more (explicit Dusart bounds are not in Mathlib).

**Review level.** `rechecked`.
**Prior art.** New; follows in a few lines from Dusart's 1999 bounds plus a finite check, but no source found states it. [A074766](https://oeis.org/A074766) still has the conjecture. Searched OEIS entry, references and history, web. Checked 2026-11-04.
