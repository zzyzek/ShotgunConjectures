/-
NT-B16.6 (Guy, UPINT 3rd ed., B16, Myerson): for non-prime d, the analogue
of the Ankeny–Artin–Chowla conjecture (d ∤ u, where (t, u) is the least
positive solution of t^2 − d u^2 = 1) fails; are 46 and 430 the two
smallest counterexamples?  Yes.

Checked here (core Lean, no Mathlib; `decide`):
* `pell_46`, `pell_430`: 24335^2 − 46·3588^2 = 1 with 46 ∣ 3588, and
  2862251^2 − 430·138030^2 = 1 with 430 ∣ 138030;
Not checked here: that these are the least solutions (continued fractions;
brute force for d = 46 in certificate/b166_check.py), and that for every other
non-square non-prime d < 430 the least solution has d ∤ u (continued-fraction
computation, certificate/b166_check.py).
-/

theorem pell_46 : 24335 ^ 2 = 46 * 3588 ^ 2 + 1 ∧ 3588 % 46 = 0 := by decide
theorem pell_430 : 2862251 ^ 2 = 430 * 138030 ^ 2 + 1 ∧ 138030 % 430 = 0 := by decide
