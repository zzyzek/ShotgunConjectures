# OEIS A083452: n written n times exceeds n^n

**Source.** [A083452](https://oeis.org/A083452) (a(n) = (n concatenated n times − n^n)/n), comment:
"Conjecture: All the terms are all positive for n>1. (n times concatenation of n with itself > n^n), n>1."
(OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial.

**Argument.** Let n have d digits, so n < 10^d. The n-fold concatenation is at least n·10^(d(n−1)), while
n^n = n·n^(n−1) < n·10^(d(n−1)) for n ≥ 2.

**Evidence.**
- Lean: [`A083452.lean`](A083452.lean) proves n^n < cat(n, d, n) for all n ≥ 2, n < 10^d.
  Nothing outside Lean.
- `certificate/check.py`: n < 1000.

**Review level.** `lean-proof`.
**Prior art.** No source found; trivial. [A083452](https://oeis.org/A083452) still has the conjecture. Searched OEIS entry, references and history. Checked 2026-11-04.
