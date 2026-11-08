import Mathlib

/-
OEIS-A230496 (Mathlib). a(n) = least odd odious k > 1 with k, k^2, ..., k^n all odious, or 0 if
there is none (odious: odd number of 1s in binary). Conjecture in the entry: a(n) > 0 for all n.

Main theorem `A230496_main`: for every n there is an odd k > 1, odious, with k^i odious for
1 ≤ i ≤ n. Hence a(n) > 0.

Construction (README). r = 2^(n+1) blocks indexed by Option (ZMod r), B = n + 2,
φ : Option (ZMod r) ≃ Fin (r+1) with φ none = 0, e(b) = B^(φ b) - 1, M = (r+1)^(n+1),
k = Σ_b 2^(M e(b)). For i ≤ n the multinomial theorem gives k^i = Σ_β mult(β) 2^(M E(β))
over compositions β of i ≤ n + 1, E(β) = Σ_b e(b) β(b) is injective (base-B digits) and every
mult(β) ≤ (r+1)^i < 2^M, so the binary weight of k^i is Σ_β s(mult(β)) (`s_blocks_fiber`).
Rotating the blocks (b ↦ b + 1 on ZMod r, fixing none) preserves mult; iterating the
involutions β ↦ β ∘ (+2^l) (l = n, ..., 0) shows that this sum is ≡ s(mult) summed over the
rotation-invariant compositions (`parity_sum`), and the only one is i at none, with mult 1.

Outside Lean: none.
-/

open Finset

/-- Number of 1s in the binary expansion of x (A000120). -/
def binWeight (x : ℕ) : ℕ := (Nat.digits 2 x).sum

/-- Odious: odd number of 1s in binary. -/
def Odious (x : ℕ) : Prop := Odd (binWeight x)

/-! ## Carry-free binary weight -/

lemma bw_add_shift (a b L : ℕ) (ha : a < 2 ^ L) :
    binWeight (a + 2 ^ L * b) = binWeight a + binWeight b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [binWeight]
  have hlen : (Nat.digits 2 a).length ≤ L := (Nat.digits_length_le_iff (by norm_num) a).2 ha
  have h := Nat.digits_append_zeroes_append_digits (b := 2) (k := L - (Nat.digits 2 a).length)
    (n := a) (m := b) (by norm_num) hb
  rw [show (Nat.digits 2 a).length + (L - (Nat.digits 2 a).length) = L by omega] at h
  unfold binWeight
  rw [← h]
  simp

lemma blocks_lt (M N : ℕ) (d : ℕ → ℕ) (hd : ∀ j, d j < 2 ^ M) :
    ∑ j ∈ range N, d j * 2 ^ (M * j) < 2 ^ (M * N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have h1 := hd N
    have e : 2 ^ (M * (N + 1)) = 2 ^ M * 2 ^ (M * N) := by rw [mul_add, mul_one, pow_add, mul_comm]
    rw [e]
    have : (d N + 1) * 2 ^ (M * N) ≤ 2 ^ M * 2 ^ (M * N) := Nat.mul_le_mul_right _ h1
    nlinarith

lemma bw_blocks (M N : ℕ) (d : ℕ → ℕ) (hd : ∀ j, d j < 2 ^ M) :
    binWeight (∑ j ∈ range N, d j * 2 ^ (M * j)) = ∑ j ∈ range N, binWeight (d j) := by
  induction N with
  | zero => simp [binWeight]
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, ← ih, mul_comm (d N),
      bw_add_shift _ _ _ (blocks_lt M N d hd)]

lemma fiber_aux {α : Type*} (F : Finset α) (c : α → ℕ) (M : ℕ) (hF : F.card ≤ 1)
    (hc : ∀ x ∈ F, c x < 2 ^ M) :
    ∑ x ∈ F, c x < 2 ^ M ∧ binWeight (∑ x ∈ F, c x) = ∑ x ∈ F, binWeight (c x) := by
  rcases F.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp [binWeight]
  · have hFx : F = {x} :=
      Finset.eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => Finset.card_le_one.1 hF y hy x hx⟩
    subst hFx
    simpa using hc x hx

/-- Carry-free sum: distinct exponents E, coefficients below 2^M. -/
lemma s_blocks_fiber {α : Type*} [DecidableEq α] (S : Finset α) (c E : α → ℕ) (M N : ℕ)
    (hc : ∀ x ∈ S, c x < 2 ^ M) (hE : ∀ x ∈ S, E x < N) (hinj : Set.InjOn E S) :
    binWeight (∑ x ∈ S, c x * 2 ^ (M * E x)) = ∑ x ∈ S, binWeight (c x) := by
  set d : ℕ → ℕ := fun j => ∑ x ∈ S with E x = j, c x
  have hfib : ∀ j, (S.filter (fun x => E x = j)).card ≤ 1 := by
    intro j
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [mem_filter] at ha hb
    exact hinj ha.1 hb.1 (ha.2.trans hb.2.symm)
  have hcf : ∀ j, ∀ x ∈ S.filter (fun x => E x = j), c x < 2 ^ M :=
    fun j x hx => hc x (mem_filter.1 hx).1
  have hd : ∀ j, d j < 2 ^ M := fun j => (fiber_aux _ c M (hfib j) (hcf j)).1
  have hmaps : ∀ x ∈ S, E x ∈ range N := fun x hx => mem_range.2 (hE x hx)
  calc binWeight (∑ x ∈ S, c x * 2 ^ (M * E x))
      = binWeight (∑ j ∈ range N, d j * 2 ^ (M * j)) := by
        congr 1
        rw [← Finset.sum_fiberwise_of_maps_to hmaps]
        refine sum_congr rfl fun j _ => ?_
        simp only [d, sum_mul]
        refine sum_congr rfl fun x hx => ?_
        rw [(mem_filter.1 hx).2]
    _ = ∑ j ∈ range N, binWeight (d j) := bw_blocks M N d hd
    _ = ∑ j ∈ range N, ∑ x ∈ S with E x = j, binWeight (c x) :=
        sum_congr rfl fun j _ => (fiber_aux _ c M (hfib j) (hcf j)).2
    _ = ∑ x ∈ S, binWeight (c x) := Finset.sum_fiberwise_of_maps_to hmaps _

/-! ## Rotation parity -/

/-- Block indices: none (the block 2^0) and r = 2^T rotating blocks. -/
abbrev Idx (T : ℕ) := Option (ZMod (2 ^ T))

/-- Rotation b ↦ b + m of the rotating blocks. -/
def rho (T : ℕ) (m : ZMod (2 ^ T)) : Idx T ≃ Idx T := Equiv.optionCongr (Equiv.addRight m)

def rot (T : ℕ) (m : ZMod (2 ^ T)) (β : Idx T → ℕ) : Idx T → ℕ := fun x => β (rho T m x)

lemma rot_rot (T : ℕ) (a b : ZMod (2 ^ T)) (β : Idx T → ℕ) :
    rot T a (rot T b β) = rot T (a + b) β := by
  funext x; cases x <;> simp [rot, rho, add_assoc]

lemma rot_zero (T : ℕ) (β : Idx T → ℕ) : rot T 0 β = β := by
  funext x; cases x <;> simp [rot, rho]

lemma sum_rot (T : ℕ) (m : ZMod (2 ^ T)) (β : Idx T → ℕ) :
    ∑ x, rot T m β x = ∑ x, β x := Equiv.sum_comp (rho T m) β

lemma mult_rot (T : ℕ) (m : ZMod (2 ^ T)) (β : Idx T → ℕ) :
    Nat.multinomial univ (rot T m β) = Nat.multinomial univ β := by
  unfold Nat.multinomial
  rw [sum_rot]
  congr 1
  exact Equiv.prod_comp (rho T m) (fun x => (β x).factorial)

/-- Compositions of i fixed by the rotation by 2^l. -/
def Fl (T i l : ℕ) : Finset (Idx T → ℕ) :=
  (piAntidiag univ i).filter (fun β => rot T (2 ^ l) β = β)

lemma rot_mem (T i : ℕ) (m : ZMod (2 ^ T)) (β : Idx T → ℕ) (h : β ∈ piAntidiag univ i) :
    rot T m β ∈ piAntidiag univ i := by
  rw [mem_piAntidiag] at h ⊢
  exact ⟨by rw [sum_rot]; exact h.1, fun _ _ => mem_univ _⟩

lemma step (T i l : ℕ) :
    (∑ β ∈ Fl T i (l + 1), (binWeight (Nat.multinomial univ β) : ZMod 2)) =
      ∑ β ∈ Fl T i l, (binWeight (Nat.multinomial univ β) : ZMod 2) := by
  rw [← sum_filter_add_sum_filter_not (Fl T i (l + 1)) (fun β => rot T (2 ^ l) β = β)]
  have hsq : ∀ β : Idx T → ℕ, rot T (2 ^ l) (rot T (2 ^ l) β) = rot T (2 ^ (l + 1)) β := by
    intro β; rw [rot_rot, pow_succ, mul_two]
  have h1 : (Fl T i (l + 1)).filter (fun β => rot T (2 ^ l) β = β) = Fl T i l := by
    ext β
    simp only [Fl, mem_filter]
    constructor
    · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      refine ⟨⟨h, ?_⟩, h'⟩
      rw [← hsq, h', h']
  have h2 : ∑ β ∈ (Fl T i (l + 1)).filter (fun β => ¬ rot T (2 ^ l) β = β),
      (binWeight (Nat.multinomial univ β) : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun β _ => rot T (2 ^ l) β) ?_ ?_ ?_ ?_
    · intro β _
      rw [mult_rot]
      exact CharTwo.add_self_eq_zero _
    · intro β hβ _
      exact (mem_filter.1 hβ).2
    · intro β hβ
      simp only [Fl, mem_filter] at hβ ⊢
      refine ⟨⟨rot_mem T i _ β hβ.1.1, ?_⟩, ?_⟩
      · rw [rot_rot, add_comm, ← rot_rot, hβ.1.2]
      · rw [hsq, hβ.1.2]; exact fun h => hβ.2 h.symm
    · intro β hβ
      simp only [Fl, mem_filter] at hβ
      rw [hsq, hβ.1.2]
  rw [h1, h2, add_zero]

lemma Fl_top (T i : ℕ) : Fl T i T = piAntidiag univ i := by
  have h0 : (2 : ZMod (2 ^ T)) ^ T = 0 := by
    have := ZMod.natCast_self (2 ^ T)
    push_cast at this
    exact this
  unfold Fl
  rw [h0]
  exact filter_true_of_mem fun β _ => rot_zero T β

lemma Fl_zero (T i : ℕ) (hi : i < 2 ^ T) : Fl T i 0 = {Pi.single none i} := by
  ext β
  simp only [Fl, mem_filter, mem_piAntidiag, mem_univ, pow_zero, mem_singleton]
  constructor
  · rintro ⟨⟨hsum, _⟩, hrot⟩
    have key : ∀ j : ℕ, β (some (j : ZMod (2 ^ T))) = β (some 0) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have := congrFun hrot (some (j : ZMod (2 ^ T)))
        simp only [rot, rho, Equiv.optionCongr_apply, Option.map_some, Equiv.coe_addRight] at this
        push_cast
        rw [this, ih]
    have hc : ∀ x : ZMod (2 ^ T), β (some x) = β (some 0) := by
      intro x; rw [← ZMod.natCast_zmod_val x]; exact key _
    have hs : i = β none + 2 ^ T * β (some 0) := by
      rw [← hsum, Fintype.sum_option]
      simp_rw [hc]
      simp [ZMod.card]
    have hz : β (some 0) = 0 := by
      by_contra h
      have h1 : 1 ≤ β (some 0) := Nat.pos_of_ne_zero h
      have : 2 ^ T ≤ 2 ^ T * β (some 0) := Nat.le_mul_of_pos_right _ h1
      omega
    have hn : β none = i := by rw [hz, mul_zero, add_zero] at hs; exact hs.symm
    funext x
    cases x with
    | none => simp [hn]
    | some x => simp [hc x, hz]
  · rintro rfl
    refine ⟨⟨by simp, by simp⟩, ?_⟩
    funext x
    cases x <;> simp [rot, rho, Pi.single_apply]

lemma binWeight_one : binWeight 1 = 1 := by norm_num [binWeight]

/-- The binary weights of the multinomial coefficients of compositions of i < 2^T into
2^T + 1 parts have odd sum. -/
lemma parity_sum (T i : ℕ) (hi : i < 2 ^ T) :
    Odd (∑ β ∈ piAntidiag (univ : Finset (Idx T)) i, binWeight (Nat.multinomial univ β)) := by
  have hall : ∀ l, (∑ β ∈ Fl T i l, (binWeight (Nat.multinomial univ β) : ZMod 2)) =
      ∑ β ∈ Fl T i 0, (binWeight (Nat.multinomial univ β) : ZMod 2) := by
    intro l
    induction l with
    | zero => rfl
    | succ l ih => rw [step, ih]
  have h := hall T
  rw [Fl_top, Fl_zero T i hi, sum_singleton, Nat.multinomial_single, binWeight_one] at h
  rw [← ZMod.natCast_eq_one_iff_odd]
  push_cast
  simpa using h

/-! ## Base-B digits are unique -/

lemma digits_unique (B : ℕ) (hB : 0 < B) : ∀ (m : ℕ) (g h : ℕ → ℕ),
    (∀ j < m, g j < B) → (∀ j < m, h j < B) →
    ∑ j ∈ range m, g j * B ^ j = ∑ j ∈ range m, h j * B ^ j → ∀ j < m, g j = h j := by
  intro m
  induction m with
  | zero => intro g h _ _ _ j hj; omega
  | succ m ih =>
    intro g h hg hh heq j hj
    have hs : ∀ f : ℕ → ℕ, ∑ j ∈ range (m + 1), f j * B ^ j =
        f 0 + B * ∑ j ∈ range m, f (j + 1) * B ^ j := by
      intro f
      rw [sum_range_succ', mul_sum, add_comm]
      simp only [pow_zero, mul_one, pow_succ]
      congr 1
      refine sum_congr rfl fun x _ => by ring
    rw [hs g, hs h] at heq
    have h0 : g 0 = h 0 := by
      have := congrArg (· % B) heq
      simp only [Nat.add_mul_mod_self_left] at this
      rwa [Nat.mod_eq_of_lt (hg 0 (by omega)), Nat.mod_eq_of_lt (hh 0 (by omega))] at this
    rw [h0] at heq
    have hrest := Nat.eq_of_mul_eq_mul_left hB (Nat.add_left_cancel heq)
    cases j with
    | zero => exact h0
    | succ j =>
      exact ih (fun j => g (j + 1)) (fun j => h (j + 1)) (fun j hj => hg _ (by omega))
        (fun j hj => hh _ (by omega)) hrest j (by omega)

/-! ## The construction -/

theorem A230496_main (n : ℕ) :
    ∃ k, Odd k ∧ 1 < k ∧ Odious k ∧ ∀ i, 1 ≤ i → i ≤ n → Odious (k ^ i) := by
  set T := n + 1
  set r := 2 ^ T
  set B := n + 2
  set M := (r + 1) ^ (n + 1)
  let φ : Idx T ≃ Fin (r + 1) :=
    (Equiv.optionCongr (ZMod.finEquiv r).symm.toEquiv).trans (finSuccEquiv r).symm
  have hφn : φ none = 0 := by simp [φ, Equiv.optionCongr]
  have hφs : ∀ x, φ (some x) = ((ZMod.finEquiv r).symm x).succ := by
    intro x; simp [φ, Equiv.optionCongr]
  set e : Idx T → ℕ := fun b => B ^ (φ b : ℕ) - 1
  set k := ∑ b, 2 ^ (M * e b)
  have hM : 1 ≤ M := Nat.one_le_pow _ _ (by omega)
  have hen : e none = 0 := by simp [e, hφn]
  have hes : ∀ x, 1 ≤ e (some x) := by
    intro x
    simp only [e, hφs]
    have : B ^ 1 ≤ B ^ (((ZMod.finEquiv r).symm x).succ : ℕ) :=
      Nat.pow_le_pow_right (by omega) (by simp)
    simp only [pow_one] at this
    omega
  have hk : k = 1 + ∑ x : ZMod (2 ^ T), 2 ^ (M * e (some x)) := by
    simp only [k]; rw [Fintype.sum_option, hen]; simp
  have hevenrest : Even (∑ x : ZMod (2 ^ T), 2 ^ (M * e (some x))) := by
    rw [even_iff_two_dvd]
    refine Finset.dvd_sum fun x _ => ?_
    exact dvd_pow_self 2 (by have := hes x; positivity)
  have hrpos : 1 ≤ ∑ x : ZMod (2 ^ T), 2 ^ (M * e (some x)) :=
    (Nat.one_le_two_pow).trans (Finset.single_le_sum (f := fun x : ZMod (2 ^ T) => 2 ^ (M * e (some x)))
      (fun _ _ => Nat.zero_le _) (mem_univ 0))
  -- Every power k^i with i ≤ n + 1 is odious.
  have hodd : ∀ i, i ≤ n + 1 → Odious (k ^ i) := by
    intro i hi
    have hir : i < 2 ^ T := Nat.lt_of_le_of_lt hi (Nat.lt_two_pow_self)
    set E : (Idx T → ℕ) → ℕ := fun β => ∑ b, e b * β b
    have hpow : k ^ i = ∑ β ∈ piAntidiag univ i, Nat.multinomial univ β * 2 ^ (M * E β) := by
      simp only [k]
      rw [sum_pow_eq_sum_piAntidiag]
      refine sum_congr rfl fun β _ => ?_
      simp only [Nat.cast_id, E]
      congr 1
      rw [mul_sum, ← prod_pow_eq_pow_sum]
      refine prod_congr rfl fun b _ => ?_
      rw [← pow_mul, mul_assoc]
    have hle : ∀ β ∈ piAntidiag (univ : Finset (Idx T)) i, ∀ b, β b ≤ i := by
      intro β hβ b
      rw [mem_piAntidiag] at hβ
      rw [← hβ.1]
      exact single_le_sum (f := β) (fun _ _ => Nat.zero_le _) (mem_univ b)
    have hmult : ∀ β ∈ piAntidiag (univ : Finset (Idx T)) i, Nat.multinomial univ β < 2 ^ M := by
      intro β hβ
      have hsum := sum_pow_eq_sum_piAntidiag (univ : Finset (Idx T)) (fun _ => (1 : ℕ)) i
      simp only [one_pow, prod_const_one, mul_one, Nat.cast_id, sum_const, card_univ,
        Fintype.card_option, ZMod.card, smul_eq_mul] at hsum
      calc Nat.multinomial univ β
          ≤ ∑ γ ∈ piAntidiag (univ : Finset (Idx T)) i, Nat.multinomial univ γ :=
            single_le_sum (f := fun γ => Nat.multinomial univ γ) (fun _ _ => Nat.zero_le _) hβ
        _ = (r + 1) ^ i := by rw [← hsum]
        _ ≤ M := Nat.pow_le_pow_right (by omega) hi
        _ < 2 ^ M := Nat.lt_two_pow_self
    have hEb : ∀ β ∈ piAntidiag (univ : Finset (Idx T)) i, E β < (∑ b, e b) * i + 1 := by
      intro β hβ
      have : E β ≤ (∑ b, e b) * i := by
        simp only [E]; rw [sum_mul]
        exact sum_le_sum fun b _ => Nat.mul_le_mul_left _ (hle β hβ b)
      omega
    -- Injectivity of E on compositions: base-B digits.
    have hdig : ∀ β : Idx T → ℕ, ∑ b, B ^ (φ b : ℕ) * β b =
        ∑ j ∈ range (r + 1), (if h : j < r + 1 then β (φ.symm ⟨j, h⟩) else 0) * B ^ j := by
      intro β
      rw [← Equiv.sum_comp φ.symm, ← Fin.sum_univ_eq_sum_range]
      refine sum_congr rfl fun j _ => ?_
      simp only [j.isLt, ↓reduceDIte, Fin.eta, Equiv.apply_symm_apply, mul_comm]
    have hEB : ∀ β ∈ piAntidiag (univ : Finset (Idx T)) i, E β + i = ∑ b, B ^ (φ b : ℕ) * β b := by
      intro β hβ
      rw [mem_piAntidiag] at hβ
      conv_lhs => rw [← hβ.1]
      simp only [E]
      rw [← sum_add_distrib]
      refine sum_congr rfl fun b _ => ?_
      have : 1 ≤ B ^ (φ b : ℕ) := Nat.one_le_pow _ _ (by omega)
      simp only [e]
      rw [Nat.sub_mul, one_mul]
      have : β b ≤ B ^ (φ b : ℕ) * β b := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hinj : Set.InjOn E (piAntidiag (univ : Finset (Idx T)) i) := by
      intro β hβ γ hγ hE
      have h1 := hEB β hβ
      have h2 := hEB γ hγ
      have heq : ∑ b, B ^ (φ b : ℕ) * β b = ∑ b, B ^ (φ b : ℕ) * γ b := by
        rw [← h1, ← h2, hE]
      rw [hdig, hdig] at heq
      have hu := digits_unique B (by omega) (r + 1) _ _
        (fun j hj => by simp only [hj, dite_true]; have := hle β hβ (φ.symm ⟨j, hj⟩); omega)
        (fun j hj => by simp only [hj, dite_true]; have := hle γ hγ (φ.symm ⟨j, hj⟩); omega) heq
      funext b
      have := hu (φ b) (φ b).isLt
      simp only [(φ b).isLt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply] at this
      exact this
    unfold Odious
    rw [hpow, s_blocks_fiber _ _ E M _ hmult hEb hinj]
    exact parity_sum T i hir
  refine ⟨k, ?_, ?_, ?_, fun i _ hi => hodd i (by omega)⟩
  · rw [hk]; exact Even.one_add hevenrest
  · rw [hk]; omega
  · simpa using hodd 1 (by omega)
