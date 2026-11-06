# OEIS A129756: roots of x^n − x^(n−1) − … − x − 1 in the right half-plane

**Source.** [A129756](https://oeis.org/A129756) (offset 0), "Repetitions of odd numbers four times",
a(n) = 1 + 2⌊n/4⌋. Comment (Michel Lagneau, Apr 09 2013): "Conjecture: number of roots of P(x) = x^n - x^(n-1) -
x^(n-2) - ... - x - 1 in the right half-plane." (OEIS text, CC BY-SA 4.0; revision #54, checked 2026-11-06.)
The companion entry [A083219](https://oeis.org/A083219) (a(n) = n − 2⌊n/4⌋) carries the same conjecture for the
left half-plane.

**Reading.** With the entry's offset 0 the index is shifted by one: the polynomial of degree n has 1 root with
positive real part for n = 1..4 and 3 for n = 5..8, i.e. a(n−1), not a(n) (a(4) = 3). So the statement holds as
"a(n) = number of roots of x^(n+1) − x^n − … − x − 1 with Re > 0" (counted with multiplicity; the roots are simple
anyway). No root lies on the imaginary axis, so "right half-plane" open or closed gives the same count.

**Result.** True with that index: for n ≥ 1, x^n − x^(n−1) − … − 1 has exactly 1 + 2⌊(n−1)/4⌋ roots with positive
real part and n − 1 − 2⌊(n−1)/4⌋ with negative real part (the A083219 comment, same shift).

**Argument.** Let P(z) = z^n − Σ_{j<n} z^j and Q(z) = (z − 1)P(z) = z^(n+1) − 2z^n + 1; Q has one more root (z = 1)
with positive real part than P.
1. *Q on the imaginary axis.* For real y, i^n(iy − 2) is iy − 2, −y − 2i, 2 − iy, y + 2i for n ≡ 0, 1, 2, 3 (mod 4),
   so Im Q(iy) = y^(n+1), −2y^n, −y^(n+1), 2y^n and Re Q(iy) = 1 − 2y^n, 1 − y^(n+1), 1 + 2y^n, 1 + y^(n+1).
   Hence Q(iy) is real only at y = 0, where Q(0) = 1. So Q has no imaginary root, and Q(iy) never meets (−∞, 0];
   arg Q(iy) (principal value) is continuous in y, and arg Q(−iy) = −arg Q(iy) (real coefficients).
2. *Argument through the roots.* Q(iy) = Π_r (iy − r) over the n + 1 roots r = a + bi (a ≠ 0). A continuous argument
   of iy − r = −a + i(y − b) is θ_r(y) = arctan((y − b)/(−a)), plus π when a > 0. The difference
   arg Q(iy) − Σ_r θ_r(y) is continuous with values in 2πℤ, so it is constant. Comparing y = Y and y = −Y:
   2 arg Q(iY) = Σ_r [θ_r(Y) − θ_r(−Y)].
3. *Y → ∞.* θ_r(Y) − θ_r(−Y) → π if a < 0 and → −π if a > 0. So 2 arg Q(iY) → π(N_L − N_R), where N_L + N_R = n + 1.
4. *Quadrant.* For Y > 1 the signs in step 1 put 2 arg Q(iY) in [π, 2π], [−2π, −π], [−π, 0], [0, π] for
   n ≡ 0, 1, 2, 3 (mod 4). So N_L − N_R lies in [1, 2], [−2, −1], [−1, 0], [0, 1], and its parity is that of n + 1.
   Hence N_L − N_R = 1, −2, −1, 0, i.e. N_R(Q) = 2m, 2m + 2, 2m + 2, 2m + 2 for n = 4m, 4m + 1, 4m + 2, 4m + 3.
   Subtracting the root z = 1: N_R(P) = 1 + 2⌊(n − 1)/4⌋.
This is the argument principle along the imaginary axis, done factor by factor so that only arctan limits are needed.

**Evidence.**
- Lean (Mathlib): [`A129756_mathlib.lean`](A129756_mathlib.lean), namespace `A129756`.
  `Pp n = X^n − Σ_{j<n} X^j : ℂ[X]`, `a n = 1 + 2 * (n / 4)`. Theorems:
  `A129756_roots : (Pp (n + 1)).roots.countP (fun r => 0 < r.re) = a n` (all n);
  `P_count : 1 ≤ n → (Pp n).roots.countP (fun r => 0 < r.re) = 1 + 2 * ((n − 1) / 4)`;
  `A083219_roots : (Pp (n + 1)).roots.countP (fun r => r.re < 0) = n − 2 * (n / 4)`.
  Steps: `Q_im`, `Q_re`, `Q_slit`, `S_re_ne` (step 1); `th_angle`, `angle_sum`, `const_of_angle_zero`, `two_arg`
  (step 2); `D_tendsto`, `limit_eq` (step 3); `count_Q`, `count_P_Q` (step 4). Roots are `Polynomial.roots` over ℂ
  (with multiplicity), factorisation from `prod_multiset_X_sub_C_of_monic_of_roots_card_eq`.
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings. Axioms of every theorem: propext, Classical.choice,
  Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/rhp.gp`](certificate/rhp.gp) with output [`certificate/rhp.out`](certificate/rhp.out): PARI/GP
  root counts for degrees 1..120 agree with 1 + 2⌊(d−1)/4⌋; the smallest |Re| over all roots stays positive
  (about 0.0038 at degree 120).
- Outside Lean: none for the statement as read above. The index shift against the entry's offset is a reading
  choice, stated in **Reading**.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. Root location of the n-bonacci polynomial is classical: one real root in (1, 2),
all others in the open unit disk (Miles 1960, Miller 1971, Wolfram 1998; see A239566). No count of roots by half-plane
was found (web search for the polynomial with "right half-plane", the A129756/A083219 comments; Du–da Fonseca,
Czech. Math. J. 2023, studies x^n − p x^(n−1) − q x − 1 without half-plane counts). OEIS entries A129756 and A083219
still state it as a conjecture. Not in google-deepmind/formal-conjectures (no `FormalConjectures/OEIS/129756.lean`
or `83219.lean`, 2026-11-06).
