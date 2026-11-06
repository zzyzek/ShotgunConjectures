# OEIS A227145: a(F_n) = F_(n-2)

**Source.** [A227145](https://oeis.org/A227145), Frank Ruskey, Jul 04 2013: "Numbers satisfying an infinite nested
recurrence relation", a(n) = n - 1 - a(n-1) - a(a(n-2)) - a(a(a(n-3))) - ..., a(n) = 0 for n <= 1. Comment:
"Conjecture: a(F_n) = F_{n-2} for n>1". (OEIS text, CC BY-SA 4.0, revision #30 of Nov 05 2025, checked
2026-11-06.)

**Reading.** The sum runs over i = 1..n (as in the entry's Mathematica program); terms with i >= n vanish
because a(0) = 0. The Lean theorem is stated for every function a : ℤ → ℤ satisfying the recurrence, and
`exists_solution` shows there is one; `eq_C` shows it is unique.

**Result.** True: a(F_m) = F_(m-2) for every m >= 2. Known: Celaya and Ruskey (arXiv:1307.0153, Prop. 10)
proved the even case; Burcsi, Celaya and Ruskey, "An infinite nested recurrence relation that takes on
Fibonacci values at Fibonacci indices" (Fibonacci Quarterly format, copy at
sites.math.rutgers.edu/~zeilberg/akherim/ruskey15.pdf), proved both cases (their Corollary 2.2). Reproved here
with a full Lean proof.

**Argument.** (Self-contained; it follows the morphic-word picture of Celaya and Ruskey but avoids their tree.)
1. *The word.* Let sig map a letter k to the block (k+1) 0^(k+1), and let w = w_0 w_1 ... be the infinite word
   with w = 0 sig(w). With L(p) = w_0 + ... + w_(p-1) and st(p) = 1 + 2p + L(p), block p of w (positions
   st(p) .. st(p) + w_p + 1) reads w_p + 1, 0, ..., 0, and the blocks tile all positions >= 1.
2. *The candidate.* c(n) = number of nonzero letters among w_0 .. w_(n-1). The nonzero letters at positions
   >= 1 are exactly the block starts, so c(st(p)) = p, and a nonzero letter at t = st(p) has
   w_(c(t+1)-1) = w_t - 1.
3. *Iterates.* By induction on j, c^j(u+1) - c^j(u) = 1 if j <= w_u and 0 otherwise.
4. *Coverage.* For t >= 1 the number of j in 1..t with j <= w_(t-j) is 1 if w_t = 0 and 0 otherwise: such a j
   says the block starting at t - j reaches t, and blocks are disjoint.
5. *Recurrence.* Steps 3 and 4 give c(N+1) + sum_{i=1..N} c^i(N+1-i) = N by induction on N, which is the entry's
   recurrence for c. A solution of the recurrence is unique (strong induction; all iterates stay below n
   because c(m) <= m). So a = c.
6. *Fibonacci values.* L(st(p)) = L(p) + p and the letter before st(p) is 0 (p >= 1). Starting from
   L(F_1) = F_0 and L(F_2) + 1 = F_1, induction gives st(F_(2k+1)) = F_(2k+3) + 1 and st(F_(2k+2)) = F_(2k+4),
   hence c(F_(2k+3)) = F_(2k+1) and c(F_(2k+4)) = F_(2k+2); also c(F_2) = c(1) = 0.

**Evidence.**
- Lean (Mathlib): [`A227145_mathlib.lean`](A227145_mathlib.lean). Main theorem `A227145_conjecture : (∀ n ≤ 1,
  a n = 0) → (∀ n ≥ 2, a n = n - 1 - Σ_{i ∈ Icc 1 n} a^[i] (n - i)) → 2 ≤ m → a (fib m) = fib (m - 2)` for
  a : ℤ → ℤ; `exists_solution`, `eq_C`. Route: `Wl`, `w`, `w_block`, `w_st`, `w_st_add`, `cover`,
  `block_unique` (step 1); `c_st`, `c_parent` (step 2); `c_iter_step` (3); `coverage` (4); `rec_nat`, `C_rec`,
  `eq_C` (5); `fib_odd_step`, `fib_even_step`, `c_fib` (6). Check: `tools/leancheck-mathlib.sh`, exit 0, no
  warnings; axioms at most propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check_A227145.py`](certificate/check_A227145.py): computes a by the recurrence for n <= 3000,
  checks the 72 data terms, a = c, and a(F_m) = F_(m-2) for m = 2..18.
- Outside Lean: none. Not verified in Lean: agreement with the OEIS data terms (the script).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. Celaya and Ruskey, "Morphic words and nested recurrence relations",
arXiv:1307.0153, Prop. 10 (even case) and the remark after it (odd case open); F. Ruskey, IWOCA 2013 problem;
Burcsi, Celaya, Ruskey (manuscript in Fibonacci Quarterly format, about 2015): full proof via the structure of
the morphic word. The OEIS entry still lists the claim as a conjecture. Not in google-deepmind/formal-conjectures
(no `FormalConjectures/OEIS/227145.lean`) or otoi-lab/oeis-lean-proofs; no Lean proof found before this.
