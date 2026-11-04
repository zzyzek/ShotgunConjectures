import OpenProblemsLib

/-! Tests of the Korselt and Fermat parts of OpenProblemsLib. -/

open OpenProblemsLib

theorem korselt_forward (n : ℕ) (h : n.IsCarmichael) :
    Squarefree n ∧ ∀ p, p.Prime → p ∣ n → p - 1 ∣ n - 1 :=
  ⟨(korselt.mp h).2.2.1, (korselt.mp h).2.2.2⟩

theorem korselt_backward (n : ℕ) (h2 : 2 < n) (hc : ¬ n.Prime) (hs : Squarefree n)
    (hk : ∀ p, p.Prime → p ∣ n → p - 1 ∣ n - 1) : n.IsCarmichael :=
  korselt.mpr ⟨h2, hc, hs, hk⟩

theorem carmichael_561 : Nat.IsCarmichael 561 :=
  isCarmichael_of_carmichaelCheck 561 [3, 11, 17] [⟨2, 1, []⟩,
  ⟨3, 2, [(2, 1)]⟩,
  ⟨5, 2, [(2, 2)]⟩,
  ⟨11, 2, [(2, 1), (5, 1)]⟩,
  ⟨17, 3, [(2, 4)]⟩] (by decide +kernel)

theorem carmichael_561_modEq : ∀ a, a.Coprime 561 → a ^ (561 - 1) ≡ 1 [MOD 561] :=
  (isCarmichael_iff_modEq.mp carmichael_561).2.2

theorem psp_341 : Nat.FermatPsp 341 2 := fermatPsp_of_pspCheck 341 2 11 (by decide +kernel)

theorem not_psp_343 : ¬ Nat.FermatPsp 343 2 := not_fermatPsp_of_powMod 343 2 (by omega) (by omega) (by decide +kernel)

theorem cipolla_5_2 : Nat.FermatPsp ((2 ^ (2 * 5) - 1) / (2 ^ 2 - 1)) 2 :=
  (cipolla (b := 2) (p := 5) le_rfl (by norm_num) (by norm_num) (by norm_num)).1
