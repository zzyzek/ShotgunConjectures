# OEIS A173989: 2-adic valuations of A173300 follow A, A, A+1, A with A odd

**Source.** [A173989](https://oeis.org/A173989) (offset 1), J. Lowell, Mar 04 2010: a(n) is the 2-adic valuation of
A173300(n), the denominator of x^n + y^n with x = (1+√3)/2, y = (1−√3)/2 (Maple and PARI programs in the entry).
Comment: "Conjecture: always follows the pattern A, A, A+1, A, where A is an odd number." Data: 0, 0, 1, 1, 2, 1,
3, 3, 4, 3, … (OEIS text, CC BY-SA 4.0, revision of Mar 23 2026, checked 2026-11-05.)

**Reading.** The pattern starts at n = 3: (a(4j+3), a(4j+4), a(4j+5), a(4j+6)) = (A, A, A+1, A) with A = 2j+1.
a(1) = a(2) = 0 precede it.

**Result.** True: for every j ≥ 0, a(4j+3) = a(4j+4) = a(4j+6) = 2j+1 and a(4j+5) = 2j+2.

**Argument.**
1. s_n = (1+√3)^n + (1−√3)^n satisfies s_0 = s_1 = 2, s_{n+2} = 2 s_{n+1} + 2 s_n (both roots satisfy
   t² = 2t + 2), so s_n ∈ ℤ and x^n + y^n = s_n / 2^n.
2. (1+√3)² = 2(2+√3), so s_{2m} = 2^m T_m, s_{2m+1} = 2^m U_m with T_0 = U_0 = 2, T_{m+1} = T_m + U_m,
   U_{m+1} = 2T_m + 3U_m.
3. Induction on m: T_{2m} ≡ 2 (mod 4), T_{2m+1} ≡ 4 (mod 8), U_m ≡ 2 (mod 4). (From T_{2m+1} ≡ 4 (mod 8),
   U_{2m+1} ≡ 2 (mod 4): T_{2m+2} = T + U ≡ 2, U_{2m+2} = 2T + 3U ≡ 2 (mod 4), T_{2m+3} = 3T + 4U ≡ 4 (mod 8),
   U_{2m+3} = 8T + 11U ≡ 2 (mod 4), with T, U at index 2m+1.)
4. So v2(s_{4j+3}) = 2j+2, v2(s_{4j+4}) = 2j+3, v2(s_{4j+5}) = 2j+3, v2(s_{4j+6}) = 2j+5. If s_n = 2^e u with u odd and
   e ≤ n, then s_n / 2^n = u / 2^(n−e) in lowest terms, so a(n) = n − e, which gives 2j+1, 2j+1, 2j+2, 2j+1.

**Evidence.**
- Lean (Mathlib): [`A173989_mathlib.lean`](A173989_mathlib.lean). `s` is the integer recurrence; `s_real : (s n : ℝ) =
  (1+√3)^n + (1−√3)^n`; `A173300 n = ((s n : ℚ) / 2^n).den` with `A173300_real`: that rational equals
  ((1+√3)/2)^n + ((1−√3)/2)^n in ℝ; `A173989 n = padicValNat 2 (A173300 n)`. Theorems: `s_TU`, `TU_mod`,
  `A173989_of`, `A173989_closed` (the four values above for all j), `A173989_pattern : ∃ A, Odd A ∧ a(4j+3) = A ∧
  a(4j+4) = A ∧ a(4j+5) = A + 1 ∧ a(4j+6) = A`, `A173989_one`, `A173989_two` (a(1) = a(2) = 0).
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings. Axioms: propext, Classical.choice, Quot.sound (some
  lemmas fewer). No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): exact recurrence; closed form for n = 3..10000; the 78 cached OEIS
  data terms agree.
- Outside Lean: none. Not verified in Lean: agreement with the OEIS data terms beyond n ≤ 6 (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-05. The entry carries formulas proved by Max Alekseyev (Mar 16 2026): a(n) =
A102302(n) for n ≥ 7, a(n) = A116921(n) for n ≥ 3, and the g.f.; A173300 has his closed form
2^((n−1)/2) (n odd), 2^(n/2−1) (n ≡ 0 mod 4), 2^(n/2−2) (n ≡ 2 mod 4) for n ≥ 3, which gives the pattern
directly. The conjecture comment itself is still unannotated. Not in google-deepmind/formal-conjectures (no
`FormalConjectures/OEIS/173989.lean` or `173300.lean`).
