# OEIS A132827: the array is the dispersion of floor(n*phi + n + 1); the entry's FORMULA is wrong from row 4

**Source.** [A132827](https://oeis.org/A132827) (offset 0, keywords tabl, uned): "Table based upon insertion points
of n into sequence A132828 and having a specific formula", read by antidiagonals, 36 data terms 1, 3, 2, 8, 6, 4,
21, 16, 11, 5, 55, 42, 29, 14, 7, ... The FORMULA line reads A(i,j) = (b(i)+1)*F(2j) + (i-b(i))*F(2j+1) with
b = A005206 (Hofstadter G). Conjecture (Clark Kimberling, Jun 03 2011): the array is the dispersion of
f(n) = floor(n*x + n + 1), x the golden ratio. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** The insertion construction through [A132828](https://oeis.org/A132828) is not well defined (A132828
says "I am not certain this sequence is accurate"; A132827 says "I had an error in the program"), so the array is
taken to be what the entry lists: the 36 data terms, rows i >= 0, columns j >= 1, read by antidiagonals
(row 0 is 1, 3, 8, 21, 55, ...; column 1 is 1, 2, 4, 5, 7, 9, 10, 12). Dispersion as in
[A191426](https://oeis.org/A191426): with t the complement of {f(n) : n >= 1} in the positive integers, listed
increasingly, row i is t(i), f(t(i)), f(f(t(i))), ...

**Result.**
- True. The dispersion D of f satisfies D(i,j) = (b(i)+1) F(2j) + (i - b(i)) F(2j+1) for all i >= 0, j >= 1, with
  b(i) = 2i - floor(i*phi) = i - floor(i/phi) (0, 1, 1, 2, 2, 2, 3, 3, 4, ...), and its first 36 antidiagonal
  terms are the entry's data.
- The entry's FORMULA with b = A005206 is wrong for every row i >= 4: it gives A(4,1) = 6, the data have 7. With
  b(i) = i - floor(i/phi) in place of A005206 it is correct.

**Argument.** f(n) = floor(n*phi) + n + 1 = floor(n*phi^2) + 1. By Rayleigh's theorem (1/phi + 1/phi^2 = 1) the
sets {floor(n*phi)} and {floor(n*phi^2)} (n >= 1) partition the positive integers, so the complement of the range
of f is {1} together with {floor(i*phi) + 1 : i >= 1}, i.e. t(i) = floor(i*phi) + 1. Put a = floor(i*phi),
p = b(i) + 1 = 2i - a + 1, q = i - b(i) = a - i, X_j = p F(2j) + q F(2j+1). Then X_1 = p + 2q = a + 1 = t(i).
From F(m+2) - F(m) - phi F(m) = F(m+1) - phi F(m) = psi^m (psi = 1 - phi = -1/phi):
X_{j+1} - X_j - phi X_j = psi^(2j) (p + q psi) = e. From a <= i*phi < a + 1 one gets 1 <= p + q psi =
i + 1 - (a - i) phi < phi^2, and 0 < psi^(2j) <= psi^2 = 1/phi^2, so 0 < e < 1. Hence floor(phi X_j) =
X_{j+1} - X_j - 1 and f(X_j) = X_{j+1}: the closed form is the dispersion. For the FORMULA: A005206(i) =
floor((i+1)/phi) while b(i) = ceil(i/phi^2), and these agree only for i <= 3; D(i,1) = 2i - b(i) + 1 is
strictly decreasing in b, so every row i >= 4 is wrong.

**Evidence.**
- Lean (Mathlib): [`A132827_mathlib.lean`](A132827_mathlib.lean). Definitions: `f n = ⌊n φ + n + 1⌋₊`, `P`
  (complement of the range), `disp i j = f^[j] (Nat.nth P i)` (column j from 0), `b`, `hofG` (A005206 by
  G(n) = n - G(G(n-1))), `entryFormula`. Theorems: `A132827_dispersion` (disp i j = (b i + 1) F(2(j+1)) +
  (i - b i) F(2(j+1)+1) for all i, j), `nth_P` (first column, via Mathlib
  `Irrational.beattySeq_symmDiff_beattySeq_pos`), `A132827_data` (the 36 data terms are the dispersion read by
  antidiagonals), `entryFormula_wrong` (FORMULA gives 6 at row 4, column 1; the dispersion gives 7).
- Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings. Axioms: propext, Classical.choice, Quot.sound.
  No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): exact integer check of data, closed form and dispersion
  (i < 2000, j <= 14), and that the A005206 formula fails in column 1 for every 4 <= i < 2000.
- Outside Lean: that the 36 terms typed into the Lean file are the entry's data; that the A005206 formula fails for
  every row i >= 4 is proved in Lean only at i = 4 (other rows: the inequality above and check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry still states the conjecture with numerical evidence only; web search
found no proof (A287664 proves a different Kimberling conjecture). Not in google-deepmind/formal-conjectures
(no 132827 file in the tree at HEAD) or otoi-lab/oeis-lean-proofs. The method (Beatty complement plus
F(m+1) - phi F(m) = psi^m) is the standard one for Wythoff-type dispersions; the error in the FORMULA line was not
noted in the entry.
