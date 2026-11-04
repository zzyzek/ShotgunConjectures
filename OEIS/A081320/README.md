# OEIS A081320: 3-smooth part of Fibonacci numbers

**Source.** [A081320](https://oeis.org/A081320) (largest 3-smooth divisor of F(n)), comment:
"Conjecture: for n>12 and n>0 modulo 12: a(n)=a(n-12) and a(12*k)=A065331(k)*144." (OEIS text, CC BY-SA 4.0.)
C. R. Greathouse IV notes in the entry that the first part follows from strong divisibility.

**Result.** True.

**Argument.** Classical valuations (Lengyel 1995): v_2(F_n) = 0 if 3 ∤ n, 1 if n ≡ 3 (mod 6), v_2(n) + 2
if 6 | n; v_3(F_n) = 0 if 4 ∤ n, v_3(n) + 1 if 4 | n. If 12 ∤ n then v_2(F_n) ∈ {0, 1, 3} and
v_3(F_n) ∈ {0, 1} depend only on n mod 12, so a(n) = a(n − 12). For n = 12k: v_2 = v_2(k) + 4 and
v_3 = v_3(k) + 2, so a(12k) = 2^4·3^2·2^(v_2 k)·3^(v_3 k) = 144·A065331(k).

**Evidence.**
- `certificate/check.py`: n ≤ 3000.
- Lean (Mathlib): [`A081320_mathlib.lean`](A081320_mathlib.lean), theorem `A081320_conjecture`: with
  smooth3 m = 2^(v_2 m)·3^(v_3 m) (the largest 3-smooth divisor, `smooth3_spec`), smooth3(F_n) = smooth3(F_(n−12))
  for n > 12, 12 ∤ n, and smooth3(F_(12k)) = 144·smooth3(k) for k ≥ 1. The valuations v_2(F_(12k)) = v_2(k) + 4,
  v_3(F_(12k)) = v_3(k) + 2 are proved in the file from F_(2m), F_(3m) identities and `Nat.fib_gcd`. Nothing
  outside Lean.

**Review level.** `lean-proof`.
**Prior art.** Partly known. [A081320](https://oeis.org/A081320) already notes (Greathouse) that the periodic part follows from strong divisibility; the formula a(12k) = 144*A065331(k) follows in a few lines from Lengyel's 2- and 3-adic valuations of F_n (Fibonacci Quart. 33, 1995). Searched OEIS entry, references and history. Checked 2026-11-04.
