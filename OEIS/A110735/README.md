# OEIS A110735: no digit insertion makes a multiple of 101

**Source.** [A110735](https://oeis.org/A110735) (least multiple of n obtained by inserting one digit in each gap and
at both ends of n; 0 if none), comment: "Conjecture: no term is zero. ..." (OEIS text, CC BY-SA 4.0.)

**Result.** False: a(101) = 0.

**Argument.** The candidates are b1 1 b2 0 b3 1 b4 = b1·10⁶ + 10⁵ + b2·10⁴ + b3·10² + 10 + b4. Modulo 101,
100 ≡ −1, so this is (b2 + b4) − (b1 + b3) + 20 ∈ [2, 38], never 0. The scan's search found 8685 such n below
10^6 (101, 202, 303, 398, 404, …); not re-checked here.

**Evidence.**
- Lean: [`A110735.lean`](A110735.lean): all 10^4 digit choices (`decide`). Nothing outside Lean.
- `certificate/check.py`: the same check in Python.

**Review level.** `lean-proof`.
**Prior art.** Verdict new, immediate (OEIS status conjecture; searched 2026-11-04). The counterexample a(101) = 0 is not in OEIS or elsewhere found. Sources: [OEIS A110735 (fetched 2026-11-04)](https://oeis.org/A110735): still says Conjecture: no term is zero; data stops below n = 101. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; OEIS A110734, A110736, A080436; Google: A110735 insert digits multiple.
