/-
OEIS A110735 (least multiple of n of the form b1 a1 b2 a2 ... ak b(k+1), single
digits b_i inserted around the digits a_i of n; 0 if none).  Conjecture: no
term is zero.  False: a(101) = 0.

Inserting digits into 101 gives b1 1 b2 0 b3 1 b4 = b1·10^6 + 10^5 + b2·10^4
+ b3·10^2 + 10 + b4 ≡ (b2 + b4) - (b1 + b3) + 20 (mod 101), using 100 ≡ -1;
this lies in [2, 38], never 0 mod 101.

Checked here (core Lean, `decide`): `main`, all 10^4 digit choices.
Not checked here: the scan's wider search (8685 such n below 10^6).
-/

theorem main : ∀ b1, b1 < 10 → ∀ b2, b2 < 10 → ∀ b3, b3 < 10 → ∀ b4, b4 < 10 →
    (b1 * 10 ^ 6 + 10 ^ 5 + b2 * 10 ^ 4 + 0 * 10 ^ 3 + b3 * 10 ^ 2 + 1 * 10 + b4) % 101 ≠ 0 := by
  decide
