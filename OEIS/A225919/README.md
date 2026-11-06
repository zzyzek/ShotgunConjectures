# OEIS A225919: the greedy harmonic-block sequence for f(k) = 1/(k+4) is linearly recurrent

**Source.** OEIS [A225919](https://oeis.org/A225919): a(1) = 1, a(n) = least k such that
f(a(n−1)+1) + ... + f(k) > f(a(n−2)+1) + ... + f(a(n−1)) (n > 1), f(k) = 1/(k+4); a(2) = 11 from comparison with 1
(the entry's example). Comment: "Conjecture: a(n) is linearly recurrent. See A225918 for details." A225918 lists
the conjectured recurrence coefficients (4, −4, 3, −2) for this f. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Result.** True: a(n) = 4a(n−1) − 4a(n−2) + 3a(n−3) − 2a(n−4) for all n ≥ 5 (a(1..4) = 1, 11, 40, 124).

**Argument.** Let r(n) be the recurrence solution, x_n = r(n) + 9/2, F(k) = H_(k+4) (harmonic number), so the
rule compares F(k) − F(a(n−1)) with F(a(n−1)) − F(a(n−2)).
1. *Harmonic bounds* (D. W. DeTemple, Amer. Math. Monthly 100 (1993) 468–470):
   1/(24(m+1)^2) < H_m − ln(m + 1/2) − γ < 1/(24m^2). So F(k) = ln(k + 9/2) + γ + ε with ε of size 1/(24k^2).
2. *Sufficient conditions.* With Q_n = x_n x_(n−2) − x_(n−1)^2 and P_n = x_(n−2) − Q_n, using
   ln(1+u) ≥ u/(1+u) and ln(1−v) ≤ −v: (S1) Q_n > 0 and Q_n/(x_n x_(n−2)) > 1/(12(r(n−1)+4)^2) imply the rule
   accepts k = r(n); (S2) P_n > 0 and P_n/x_(n−1)^2 ≥ 1/(24(r(n)+3)^2) + 1/(24(r(n−2)+4)^2) imply it rejects
   k = r(n) − 1. So, by induction, a(n) = r(n).
3. *Small n.* (S1), (S2) hold for 3 ≤ n ≤ 60 (exact rational arithmetic).
4. *Large n.* u_n = r(n) + 13/3 satisfies u_n = 3u_(n−1) − u_(n−2) + 2u_(n−3), whose characteristic polynomial is
   (x − R)(x^2 − (3−R)x + 2/R), R ≈ 2.89329 the real root of x^3 − 3x^2 + x − 2. For w_n = u_n − R u_(n−1) and λ
   a complex root of the quadratic (|λ|^2 = 2/R < 1), z_n = w_n − λ̄ w_(n−1) = λ z_(n−1), so |w_(n−1)| ≤
   |z_N|/Im λ for n ≥ N. Exactly, e_n := Q_n/x_(n−2) = (R−1)^2/6 + w_n − R w_(n−1) − (w_(n−1) − (R−1)/6)^2/x_(n−2).
   At N = 60 interval arithmetic gives |e_n − (R−1)^2/6| ≤ 1.1·10^(−5) for n > 60, with (R−1)^2/6 ≈ 0.5974; so
   0.3 ≤ e_n ≤ 0.9, and also x_n ≤ 3x_(n−1), x_(n−2) ≥ 30. Then (S1): Q_n/(x_n x_(n−2)) = e_n/x_n ≥ 0.1/x_(n−1)
   > 1/(3x_(n−1)^2); (S2): P_n/x_(n−1)^2 = x_(n−2)(1 − e_n)/x_(n−1)^2 ≥ 1/(90 x_(n−2)) ≥ 1/(6 x_(n−2)^2), which
   bounds the right side.

**Evidence.**
- [`certificate/proof_check.py`](certificate/proof_check.py) (Python, exact fractions plus mpmath interval
  arithmetic): the data, the base step a(2) = 11, (S1) and (S2) for 3 ≤ n ≤ 60, the cubic recurrence for u, an
  exact-formula spot check, and the tail bounds of step 4. Output in `certificate/out.txt`.
- Independent check (scan scratch): the greedy rule computed with 120-digit digamma values for 70 terms agrees with
  the recurrence.
- Outside Lean: everything (no Lean file); DeTemple's inequality is cited, not reproved.

**Review level.** `rechecked` (argument re-derived; finite and interval parts machine-checked in Python).

**Prior art.** Checked 2026-11-06: OEIS A225918–A225922 entries (M. Alekseyev 2022: for A225920–A225922 no
recurrence of order below 50; a ceiling formula for A225919 "unless the fractional part ... is very small");
C. Kimberling, "Unsolved Problems and Rewards" (no entry for these). No proof found. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
