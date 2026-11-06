# OEIS A179902: the parity pattern 1, 0, 1, 1 (period 4) holds

**Source.** [A179902](https://oeis.org/A179902) (offset 1), "Row sums of triangle A179901." Comment:
"Conjectured mod 2 parity: (1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1,...)." Formula by Andrew Howroyd
(Sep 21 2025): a(n) = (n^4 - 8n^3 + 35n^2 - 52n + 36)/12. [A179901](https://oeis.org/A179901):
"Triangle read by rows, antidiagonals of an array generated from (1, r, r, r, ...) convolved with
(1, 0, r, r, r, ...)." (OEIS text, CC BY-SA 4.0; A179902 revision #23 of Jul 20 2026, A179901 #14,
checked 2026-11-06.)

**Reading.** Array row r >= 1 is the coefficient list of the product of (1, r, r, ...) and
(1, 0, r, r, ...): 1, r, 2r, 2r + r^2, 2r + 2r^2, ... (column m + 1 holds 2r + r^2 (m - 2) for
m >= 2). Row n of the triangle is (A(n,1), A(n-1,2), ..., A(1,n)), as in the entry's example and
Howroyd's PARI program; this reproduces the triangle data and the A179902 data. The conjecture says
a(n) is even exactly when n = 2 (mod 4).

**Result.** True for every n >= 1: a(n) is even iff n = 2 (mod 4).

**Argument.** Coefficient m + 2 of the product is r (from 1 * r) + r (from r * 1) + 0 (from r * 0)
+ m r^2 (the middle terms), so it is 2r + r^2 m. Row n of the triangle is 1, n - 1, then
2(n - 2 - i) + (n - 2 - i)^2 i for i = 0..n - 3; summing with the power sums of i, i^2, i^3 gives
12 a(n) = n^4 - 8n^3 + 35n^2 - 52n + 36 (Howroyd's formula). Then 12(a(n+4) - a(n)) =
8(2n^3 + 19n + 12), so 3(a(n+4) - a(n)) is even and so is a(n+4) - a(n). With a(1..4) = 1, 2, 5, 11
the parities repeat 1, 0, 1, 1.

**Evidence.**
- Lean (Mathlib): [`A179902_mathlib.lean`](A179902_mathlib.lean). `arr r m` is coefficient m of the
  product of the two sequences (a literal finite convolution), `T n k = arr (n + 1 - k) (k - 1)`,
  `A179902 n = ∑_{k ∈ [1, n]} T n k`. Main theorem `A179902_parity : 1 ≤ n → A179902 n % 2 =
  if n % 4 = 2 then 0 else 1`; also `A179902_closed` (Howroyd's formula), via `arr_two`, `s1`, `s2`,
  `s3`, `G_eq`, `step4`. Checked with `tools/leancheck-mathlib.sh`: OK, no warnings; axioms propext,
  Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.py`](certificate/check.py): rebuilds the triangle (78 data terms) and the row
  sums (42 data terms) from the convolution; closed form and parity for n <= 300.
- Outside Lean: the reading of "antidiagonals" (row n read from array row n down to array row 1),
  fixed by the entry's example; agreement with the OEIS data terms (check.py).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry still marks the parity as conjectured. Howroyd's closed
form (2025) and E. R. Oliveira's g.f. and recurrence (2026) are in the entry, stated without proof;
the parity follows from the closed form in two lines but is not drawn there. Web search found nothing
further. Not in google-deepmind/formal-conjectures (tree at HEAD 2026-11-06) or
otoi-lab/oeis-lean-proofs.
