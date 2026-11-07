import OpenProblemsLib.Fermat
import Mathlib.Tactic.NormNum

/-
COM-P127 (Mathlib). Coman, problem 127: are there Poulet numbers P2 = 2*P1 - 1, with P1
also a Poulet number, other than 130561 = 2*65281 - 1?

Main theorem `P127_main`: yes. 31417 = 2*15709 - 1 and 41541241 = 2*20770621 - 1, with all
four numbers Fermat pseudoprimes to base 2 (Mathlib `Nat.FermatPsp _ 2`), checked by a
kernel `powMod` computation with an explicit proper divisor (lib Fermat).

Checked: the whole statement above. Not checked here: the count 27 below 10^13
(certificate in ../P126/certificate/scan.py) and the infinitude conjecture C178.
-/

open OpenProblemsLib

/-- Coman's property: `P2` is Poulet and `P2 = 2*P1 - 1` with `P1` Poulet. -/
def ComanDoublePoulet (P2 : ℕ) : Prop :=
  Nat.FermatPsp P2 2 ∧ ∃ P1, Nat.FermatPsp P1 2 ∧ P2 = 2 * P1 - 1

theorem poulet_130561 : ComanDoublePoulet 130561 :=
  ⟨fermatPsp_of_pspCheck 130561 2 137 (by decide +kernel), 65281,
    fermatPsp_of_pspCheck 65281 2 97 (by decide +kernel), by norm_num⟩

theorem poulet_31417 : ComanDoublePoulet 31417 :=
  ⟨fermatPsp_of_pspCheck 31417 2 89 (by decide +kernel), 15709,
    fermatPsp_of_pspCheck 15709 2 23 (by decide +kernel), by norm_num⟩

theorem poulet_41541241 : ComanDoublePoulet 41541241 :=
  ⟨fermatPsp_of_pspCheck 41541241 2 7 (by decide +kernel), 20770621,
    fermatPsp_of_pspCheck 20770621 2 1861 (by decide +kernel), by norm_num⟩

theorem P127_main : ∃ P2, P2 ≠ 130561 ∧ ComanDoublePoulet P2 :=
  ⟨31417, by norm_num, poulet_31417⟩
