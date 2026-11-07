import OpenProblemsLib.Fermat
import Mathlib.Tactic.NormNum.Prime

/-
COM-P126 (Mathlib). Coman, problem 126: are there Poulet numbers P = (d^2 + d)/2, with
d a prime factor of P, other than 2701 = (73^2 + 73)/2?

Main theorem `P126_main`: yes. 18721 = (193^2 + 193)/2 and 33153 = (257^2 + 257)/2 are
Fermat pseudoprimes to base 2 (Mathlib `Nat.FermatPsp _ 2`), 193 and 257 are prime and
divide them. Base-2 pseudoprimality by a kernel `powMod` computation (lib Fermat),
primality by `norm_num`.

Checked: the whole statement above. Not checked here: the count 7988 below 10^13
(certificate/scan.py over the Feitsma-Galway list) and the infinitude conjecture C177.
-/

open OpenProblemsLib

/-- Coman's property: `P` is a Poulet number of the form (d^2 + d)/2, d a prime factor. -/
def ComanTriPoulet (P : ℕ) : Prop :=
  Nat.FermatPsp P 2 ∧ ∃ d, Nat.Prime d ∧ d ∣ P ∧ P = (d ^ 2 + d) / 2

theorem poulet_2701 : ComanTriPoulet 2701 :=
  ⟨fermatPsp_of_pspCheck 2701 2 37 (by decide +kernel), 73, by norm_num, by norm_num, by norm_num⟩

theorem poulet_18721 : ComanTriPoulet 18721 :=
  ⟨fermatPsp_of_pspCheck 18721 2 97 (by decide +kernel), 193, by norm_num, by norm_num, by norm_num⟩

theorem poulet_33153 : ComanTriPoulet 33153 :=
  ⟨fermatPsp_of_pspCheck 33153 2 3 (by decide +kernel), 257, by norm_num, by norm_num, by norm_num⟩

theorem P126_main : ∃ P, P ≠ 2701 ∧ ComanTriPoulet P :=
  ⟨18721, by norm_num, poulet_18721⟩
