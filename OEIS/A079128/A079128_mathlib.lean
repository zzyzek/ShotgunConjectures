import Mathlib

/-
OEIS A079128: number of degree-n permutations with (mutually) relatively prime cycle lengths.
Conjecture (V. Jovovic, Jan 25 2003): gcd(a(n), n) = 1.

Definitions.  `RP σ`: every d dividing all cycle lengths (minimal periods of all points) is 1.
`A079128 n = Nat.card {σ : Perm (Fin n) // RP σ}`.
Main theorem.  `A079128_coprime : 1 ≤ n → Nat.Coprime (A079128 n) n`.
Route.  For a prime p with n = p m, relabel Fin n as Fin m × ZMod p (`card_RP_congr`).
The p-group G = (ZMod p)^m acts on the RP permutations by conjugation with the block shifts
rho s (i, x) = (i, x + s i) (RP is conjugation invariant, `RP_permCongr`), so
a(n) ≡ #fixed points (mod p) (Mathlib `IsPGroup.card_modEq_card_fixedPoints`).
A permutation commuting with all shifts is a shift (`eq_rho_of_commute`), and rho s is RP
iff some s i = 0 (`RP_rho_iff`), so #fixed points = p^m - (p-1)^m (`card_fixedPoints`),
which is not divisible by p (`not_dvd_card_exists_zero`).
Not checked here: agreement of `A079128` with the data terms (certificate/check.py).
-/

open Function Equiv

namespace A079128

/-- σ has (mutually) relatively prime cycle lengths: the only common divisor of all
cycle lengths (the minimal periods of the points) is 1. -/
def RP {β : Type*} (σ : Perm β) : Prop := ∀ d : ℕ, (∀ x, d ∣ minimalPeriod σ x) → d = 1

lemma iterate_permCongr {β γ : Type*} (e : β ≃ γ) (σ : Perm β) (k : ℕ) (x : β) :
    (e.permCongr σ)^[k] (e x) = e (σ^[k] x) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply', ih, iterate_succ_apply']; simp [Equiv.permCongr_apply]

lemma minimalPeriod_permCongr {β γ : Type*} (e : β ≃ γ) (σ : Perm β) (x : β) :
    minimalPeriod (e.permCongr σ) (e x) = minimalPeriod σ x := by
  rw [minimalPeriod_eq_minimalPeriod_iff]
  intro k
  simp only [IsPeriodicPt, IsFixedPt, iterate_permCongr, e.apply_eq_iff_eq]

lemma RP_permCongr {β γ : Type*} (e : β ≃ γ) (σ : Perm β) : RP (e.permCongr σ) ↔ RP σ := by
  constructor
  · intro h d hd
    exact h d (fun y => by rw [← e.apply_symm_apply y, minimalPeriod_permCongr]; exact hd _)
  · intro h d hd
    exact h d (fun x => by rw [← minimalPeriod_permCongr e]; exact hd _)

lemma card_RP_congr {β γ : Type*} [Fintype β] [Fintype γ] (e : β ≃ γ) :
    Nat.card {σ : Perm β // RP σ} = Nat.card {σ : Perm γ // RP σ} :=
  Nat.card_congr (e.permCongr.subtypeEquiv (fun σ => (RP_permCongr e σ).symm))

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

/-- Shift permutation of Fin m × ZMod p: (i, x) ↦ (i, x + s i). -/
def rho (s : Fin m → ZMod p) : Perm (Fin m × ZMod p) where
  toFun y := (y.1, y.2 + s y.1)
  invFun y := (y.1, y.2 - s y.1)
  left_inv y := by simp
  right_inv y := by simp

lemma rho_apply (s : Fin m → ZMod p) (y : Fin m × ZMod p) : rho s y = (y.1, y.2 + s y.1) := rfl

lemma rho_add (s t : Fin m → ZMod p) : rho (s + t) = rho s * rho t := by
  ext y <;> simp [rho_apply, Perm.mul_apply, add_assoc, add_comm (t y.1)]

lemma rho_zero : rho (0 : Fin m → ZMod p) = 1 := by ext y <;> simp [rho_apply]

lemma rho_iterate (s : Fin m → ZMod p) (k : ℕ) (y : Fin m × ZMod p) :
    (rho s)^[k] y = (y.1, y.2 + k * s y.1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterate_succ_apply', ih, rho_apply]; push_cast; ext <;> simp; ring

lemma RP_rho_iff (s : Fin m → ZMod p) : RP (rho s) ↔ ∃ i, s i = 0 := by
  constructor
  · intro h
    by_contra hall
    push Not at hall
    have := h p (fun y => ?_)
    · exact hp.out.one_lt.ne' this
    · have hper := isPeriodicPt_minimalPeriod (rho s) y
      unfold IsPeriodicPt IsFixedPt at hper
      rw [rho_iterate] at hper
      have h0 : ((minimalPeriod (rho s) y : ℕ) : ZMod p) * s y.1 = 0 := by
        have := congrArg Prod.snd hper; simpa using this
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact (ZMod.natCast_eq_zero_iff _ _).mp h1
      · exact absurd h1 (hall _)
  · rintro ⟨i, hi⟩ d hd
    have h1 : minimalPeriod (rho s) (i, 0) = 1 := by
      rw [minimalPeriod_eq_one_iff_isFixedPt]
      simp [IsFixedPt, rho_apply, hi]
    exact Nat.dvd_one.mp (h1 ▸ hd (i, 0))

/-- The p-group acting by conjugation. -/
abbrev G (p m : ℕ) := Multiplicative (Fin m → ZMod p)

def rhoG (g : G p m) : Perm (Fin m × ZMod p) := rho (Multiplicative.toAdd g)

lemma rhoG_mul (g h : G p m) : rhoG (g * h) = rhoG g * rhoG h := rho_add _ _
lemma rhoG_one : rhoG (1 : G p m) = 1 := rho_zero

abbrev S (p m : ℕ) := {σ : Perm (Fin m × ZMod p) // RP σ}

omit hp in
lemma conj_eq_permCongr (g : Perm (Fin m × ZMod p)) (σ : Perm (Fin m × ZMod p)) :
    g * σ * g⁻¹ = g.permCongr σ := Equiv.ext fun _ => rfl

instance : MulAction (G p m) (S p m) where
  smul g σ := ⟨rhoG g * σ.1 * (rhoG g)⁻¹, by rw [conj_eq_permCongr, RP_permCongr]; exact σ.2⟩
  one_smul σ := by apply Subtype.ext; show rhoG 1 * σ.1 * (rhoG 1)⁻¹ = σ.1; simp [rhoG_one]
  mul_smul g h σ := by
    apply Subtype.ext
    show rhoG (g * h) * σ.1 * (rhoG (g * h))⁻¹ = rhoG g * (rhoG h * σ.1 * (rhoG h)⁻¹) * (rhoG g)⁻¹
    rw [rhoG_mul]; group

lemma smul_val (g : G p m) (σ : S p m) : (g • σ).1 = rhoG g * σ.1 * (rhoG g)⁻¹ := rfl

/-- A permutation commuting with every shift is a shift. -/
lemma eq_rho_of_commute (σ : Perm (Fin m × ZMod p)) (h : ∀ s, rho s * σ = σ * rho s) :
    ∃ s, σ = rho s := by
  have hc : ∀ s y, σ (rho s y) = rho s (σ y) := by
    intro s y; have := congrArg (fun f : Perm _ => f y) (h s); simp [Perm.mul_apply] at this
    exact this.symm
  -- σ keeps the first coordinate
  have hfst : ∀ y, (σ y).1 = y.1 := by
    intro y
    by_contra hne
    have := hc (Pi.single (σ y).1 1) y
    rw [rho_apply, rho_apply] at this
    rw [Pi.single_eq_of_ne (Ne.symm hne), Pi.single_eq_same, add_zero] at this
    have h2 := congrArg Prod.snd this
    simp at h2
  refine ⟨fun i => (σ (i, 0)).2, ?_⟩
  have key : ∀ i (k : ℕ), σ (i, (k : ZMod p)) = (i, (k : ZMod p) + (σ (i, 0)).2) := by
    intro i k
    induction k with
    | zero => ext <;> simp [hfst]
    | succ k ih =>
      have := hc (Pi.single i 1) (i, (k : ZMod p))
      rw [rho_apply, rho_apply, ih] at this
      simp only [Pi.single_eq_same] at this
      push_cast
      rw [this]; ext <;> simp; ring
  ext y
  · simp [rho_apply, hfst]
  · obtain ⟨i, x⟩ := y
    have := key i x.val
    rw [ZMod.natCast_zmod_val] at this
    simp [this, rho_apply]

lemma comm_of_fixed (σ : MulAction.fixedPoints (G p m) (S p m)) (s : Fin m → ZMod p) :
    rho s * σ.1.1 = σ.1.1 * rho s := by
  have hσ := σ.2 (Multiplicative.ofAdd s)
  have h1 := congrArg Subtype.val hσ
  rw [smul_val] at h1
  unfold rhoG at h1
  simp only [toAdd_ofAdd] at h1
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1

lemma card_fixedPoints :
    Nat.card (MulAction.fixedPoints (G p m) (S p m)) = Nat.card {s : Fin m → ZMod p // ∃ i, s i = 0} := by
  symm
  apply Nat.card_congr
  refine
    { toFun := fun s => ⟨⟨rho s.1, (RP_rho_iff s.1).mpr s.2⟩, fun g => Subtype.ext ?_⟩
      invFun := fun σ => ⟨Classical.choose (eq_rho_of_commute σ.1.1 (comm_of_fixed σ)), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · show rhoG g * rho s.1 * (rhoG g)⁻¹ = rho s.1
    unfold rhoG
    rw [mul_inv_eq_iff_eq_mul, ← rho_add, ← rho_add, add_comm]
  · rw [← RP_rho_iff, ← Classical.choose_spec (eq_rho_of_commute σ.1.1 (comm_of_fixed σ))]
    exact σ.1.2
  · intro s
    apply Subtype.ext
    have hspec := Classical.choose_spec (eq_rho_of_commute (rho s.1)
      (fun t => by rw [← rho_add, ← rho_add, add_comm]))
    funext i
    have := congrArg (fun f : Perm _ => (f (i, 0)).2) hspec
    simpa [rho_apply] using this.symm
  · intro σ
    apply Subtype.ext; apply Subtype.ext
    exact (Classical.choose_spec (eq_rho_of_commute σ.1.1 (comm_of_fixed σ))).symm

lemma not_dvd_card_exists_zero (hm : 1 ≤ m) :
    ¬ p ∣ Nat.card {s : Fin m → ZMod p // ∃ i, s i = 0} := by
  classical
  have hp1 := hp.out.one_lt
  have hcompl : Nat.card {s : Fin m → ZMod p // ¬ ∃ i, s i = 0} = (p - 1) ^ m := by
    have e : {s : Fin m → ZMod p // ¬ ∃ i, s i = 0} ≃ (Fin m → {x : ZMod p // x ≠ 0}) :=
      (Equiv.subtypeEquivRight (fun s => by simp [not_exists])).trans (Equiv.subtypePiEquivPi)
    rw [Nat.card_congr e, Nat.card_pi]
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ZMod.card]
  have hsum : Nat.card {s : Fin m → ZMod p // ∃ i, s i = 0} + (p - 1) ^ m = p ^ m := by
    rw [← hcompl]
    simp only [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl, Fintype.card_pi]
    simp only [ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have : Fintype.card {s : Fin m → ZMod p // ∃ i, s i = 0} ≤ p ^ m := by
      calc Fintype.card {s : Fin m → ZMod p // ∃ i, s i = 0} ≤ Fintype.card (Fin m → ZMod p) :=
            Fintype.card_subtype_le _
        _ = p ^ m := by simp [ZMod.card]
    omega
  intro hdvd
  have h1 : p ∣ p ^ m := dvd_pow_self p (by omega)
  have h2 : p ∣ (p - 1) ^ m := by
    have := (Nat.dvd_sub h1 hdvd)
    rwa [← hsum, Nat.add_sub_cancel_left] at this
  have h3 : p ∣ p - 1 := hp.out.dvd_of_dvd_pow h2
  have := Nat.le_of_dvd (by omega) h3
  omega

end A079128

open A079128 in
/-- OEIS A079128: number of degree-n permutations with (mutually) relatively prime cycle
lengths, i.e. the only common divisor of all cycle lengths is 1. -/
noncomputable def A079128 (n : ℕ) : ℕ := Nat.card {σ : Equiv.Perm (Fin n) // RP σ}

open A079128 in
/-- Jovovic's conjecture: gcd(a(n), n) = 1.  More precisely a(n) ≡ p^m - (p-1)^m (mod p)
for every prime p with n = p m. -/
theorem A079128_coprime (n : ℕ) (hn : 1 ≤ n) : Nat.Coprime (A079128 n) n := by
  apply Nat.coprime_of_dvd
  intro q hq hqa hqn
  obtain ⟨m, rfl⟩ := hqn
  have : Fact q.Prime := ⟨hq⟩
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hn
    · exact h
  have e : Fin (q * m) ≃ Fin m × ZMod q :=
    Fintype.equivOfCardEq (by simp [ZMod.card, mul_comm])
  have hcard : A079128 (q * m) = Nat.card (S q m) := card_RP_congr e
  have hG : IsPGroup q (G q m) := IsPGroup.of_card (n := m) (by
    rw [Nat.card_eq_fintype_card]
    simp [G, Fintype.card_multiplicative, ZMod.card])
  have hmod := hG.card_modEq_card_fixedPoints (S q m)
  rw [hcard] at hqa
  have := (Nat.ModEq.dvd_iff hmod (dvd_refl q)).mp hqa
  rw [card_fixedPoints] at this
  exact not_dvd_card_exists_zero hm this

open A079128
