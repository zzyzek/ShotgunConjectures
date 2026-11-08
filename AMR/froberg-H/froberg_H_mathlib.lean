import Mathlib

/-!
# Problem H (Fröberg–Lundqvist–Oneto–Shapiro): the open degree of T_{n,2,2}, n = 2k

Proved here (`froberg_H_mul_ell_injective`, `froberg_H_even`): for `#σ = 2k` and
`R = ℂ[x_σ] / (x_1², …, x_n²)²`, multiplication by `ℓ = x_1 + … + x_n` is injective from
`R_{k+1}` to `R_{k+2}`. This is the one degree that Boij–Fröberg–Lundqvist's proof of the WLP
(J. Algebra 495 (2018), Theorem 22) leaves open for even `n`.

Outside Lean: BFL Theorem 22's treatment of all other degrees (and of odd `n`), which together with
this theorem gives the WLP of `T_{n,2,2}` for every `n`.

The proof is not the Specht-module argument of the README. Reading coefficients gives
`Up β = 0`, `link_i β + Up γ_i = 0`, `γ_i + Up δ_i = 0` (`froberg_core`). Only the commutator
`Dn ∘ Up - Up ∘ Dn = #(G \ S) - #S` and adjointness are used: `link_i β ∈ Im Up²` lies in
`(ker Up)^⊥ = Im Dn` on `[2k] \ {i}`, which forces `3 ‖link_i β‖² ≤ ‖Up link_i β‖² = ‖del_i β‖²`;
summing over `i` gives `3 (k+1) ‖β‖² ≤ (k-1) ‖β‖²`, so `β = 0`, and then `γ = δ = 0`.

Part 1. Boolean-lattice operators on functions `Finset α → ℝ`, relative to a ground set `G`:
`Up G f S = ∑_{x ∈ S ∩ G} f (S \ {x})`, `Dn G f S = ∑_{y ∈ G \ S} f (S ∪ {y})`.
They are adjoint for `ip f g = ∑_S f S * g S`, and `Dn ∘ Up - Up ∘ Dn` acts on a set `S` by the
scalar `#(G \ S) - #(S ∩ G)`.
-/

open Finset



variable {α : Type*} [DecidableEq α]

/-- Up operator relative to the ground set `G`. -/
def Up (G : Finset α) (f : Finset α → ℝ) (S : Finset α) : ℝ :=
  ∑ x ∈ S ∩ G, f (S.erase x)

/-- Down operator relative to the ground set `G`. -/
def Dn (G : Finset α) (f : Finset α → ℝ) (S : Finset α) : ℝ :=
  ∑ y ∈ G \ S, f (insert y S)

/-- Standard inner product of functions on finsets. -/
def ip [Fintype α] (f g : Finset α → ℝ) : ℝ :=
  ∑ S, f S * g S

/-- `f` is supported on the `t`-subsets of `G`. -/
def Lev (G : Finset α) (t : ℕ) (f : Finset α → ℝ) : Prop :=
  ∀ S, f S ≠ 0 → S ⊆ G ∧ S.card = t

/-- Restriction of `f` to the `t`-subsets of `G`. -/
def restr (G : Finset α) (t : ℕ) (f : Finset α → ℝ) (S : Finset α) : ℝ :=
  if S ⊆ G ∧ S.card = t then f S else 0

omit [DecidableEq α] in
lemma ip_comm [Fintype α] (f g : Finset α → ℝ) : ip f g = ip g f := by
  unfold ip; exact sum_congr rfl fun _ _ => mul_comm _ _

omit [DecidableEq α] in
lemma ip_self_nonneg [Fintype α] (f : Finset α → ℝ) : 0 ≤ ip f f :=
  sum_nonneg fun _ _ => mul_self_nonneg _

omit [DecidableEq α] in
lemma eq_zero_of_ip_self [Fintype α] (f : Finset α → ℝ) (h : ip f f = 0) : f = 0 := by
  funext S
  have h2 := (sum_eq_zero_iff_of_nonneg (fun S _ => mul_self_nonneg (f S))).1 h S (mem_univ _)
  simpa using h2

/-- Removing and re-inserting a point: sums over sets avoiding `i` and sets containing `i`. -/
lemma sum_avoid_eq_sum_contain [Fintype α] (i : α) (F : Finset α → ℝ) :
    (∑ T, if i ∈ T then 0 else F (insert i T)) = ∑ S, if i ∈ S then F S else 0 := by
  rw [← sum_filter, sum_ite, sum_const_zero, zero_add]
  apply sum_nbij' (fun T => insert i T) (fun S => S.erase i)
  · intro T hT; simp
  · intro S hS; simp
  · intro T hT
    simp only [mem_filter, mem_univ, true_and] at hT
    exact erase_insert hT
  · intro S hS
    simp only [mem_filter, mem_univ, true_and] at hS
    exact insert_erase hS
  · intro T _; rfl

/-- `Up G` and `Dn G` are adjoint. -/
lemma ip_Up [Fintype α] (G : Finset α) (f g : Finset α → ℝ) : ip (Up G f) g = ip f (Dn G g) := by
  unfold ip Up Dn
  have hL : ∀ S : Finset α, (∑ x ∈ S ∩ G, f (S.erase x)) * g S =
      ∑ x ∈ G, if x ∈ S then f (S.erase x) * g S else 0 := by
    intro S
    rw [sum_mul, ← sum_filter, inter_comm, filter_mem_eq_inter]
  have hR : ∀ R : Finset α, f R * (∑ y ∈ G \ R, g (insert y R)) =
      ∑ y ∈ G, if y ∈ R then 0 else f R * g (insert y R) := by
    intro R
    rw [mul_sum, ← filter_notMem_eq_sdiff, sum_filter]
    exact sum_congr rfl fun y _ => by split_ifs <;> simp_all
  simp_rw [hL, hR]
  rw [sum_comm, sum_comm (s := univ)]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_avoid_eq_sum_contain x (fun S => f (S.erase x) * g S)]
  refine sum_congr rfl fun R _ => ?_
  split_ifs with h
  · rfl
  · rw [erase_insert h]

/-- The commutator of `Dn` and `Up` is a scalar on each set. -/
lemma comm_apply (G : Finset α) (f : Finset α → ℝ) (S : Finset α) :
    Dn G (Up G f) S - Up G (Dn G f) S =
      (((G \ S).card : ℝ) - ((S ∩ G).card : ℝ)) * f S := by
  unfold Dn Up
  have h1 : ∀ y ∈ G \ S, (∑ x ∈ insert y S ∩ G, f ((insert y S).erase x)) =
      f S + ∑ x ∈ S ∩ G, f (insert y (S.erase x)) := by
    intro y hy
    rw [mem_sdiff] at hy
    rw [insert_inter_of_mem hy.1, sum_insert (fun h => hy.2 (mem_inter.1 h).1),
      erase_insert hy.2]
    congr 1
    refine sum_congr rfl fun x hx => ?_
    have hxy : y ≠ x := fun h => hy.2 (h ▸ (mem_inter.1 hx).1)
    rw [erase_insert_of_ne hxy]
  have h2 : ∀ x ∈ S ∩ G, (∑ y ∈ G \ S.erase x, f (insert y (S.erase x))) =
      f S + ∑ y ∈ G \ S, f (insert y (S.erase x)) := by
    intro x hx
    rw [mem_inter] at hx
    rw [sdiff_erase hx.2, sum_insert (fun h => (mem_sdiff.1 h).2 hx.1),
      insert_erase hx.1]
  rw [sum_congr rfl h1, sum_congr rfl h2, sum_add_distrib, sum_add_distrib, sum_const, sum_const,
    sum_comm (s := G \ S)]
  simp only [nsmul_eq_mul]
  ring

lemma Lev_Up {G : Finset α} {t : ℕ} {f : Finset α → ℝ} (h : Lev G t f) :
    Lev G (t + 1) (Up G f) := by
  intro S hS
  obtain ⟨x, hx, hfx⟩ := exists_ne_zero_of_sum_ne_zero hS
  obtain ⟨h1, h2⟩ := h _ hfx
  rw [mem_inter] at hx
  refine ⟨?_, ?_⟩
  · rw [← insert_erase hx.1]; exact insert_subset hx.2 h1
  · rw [← card_erase_add_one hx.1, h2]

lemma Lev_Dn {G : Finset α} {t : ℕ} {f : Finset α → ℝ} (h : Lev G (t + 1) f) :
    Lev G t (Dn G f) := by
  intro S hS
  obtain ⟨y, hy, hfy⟩ := exists_ne_zero_of_sum_ne_zero hS
  obtain ⟨h1, h2⟩ := h _ hfy
  rw [mem_sdiff] at hy
  refine ⟨(subset_insert y S).trans h1, ?_⟩
  rw [card_insert_of_notMem hy.2] at h2; omega

lemma Lev_restr (G : Finset α) (t : ℕ) (f : Finset α → ℝ) : Lev G t (restr G t f) := by
  intro S hS
  unfold restr at hS
  split_ifs at hS with h
  · exact h
  · exact absurd rfl hS

lemma restr_of_Lev {G : Finset α} {t : ℕ} {f : Finset α → ℝ} (h : Lev G t f) :
    restr G t f = f := by
  funext S
  unfold restr
  split_ifs with hS
  · rfl
  · by_contra hne; exact hS (h S (Ne.symm hne))

lemma ip_restr [Fintype α] {G : Finset α} {t : ℕ} {a : Finset α → ℝ} (h : Lev G t a) (x : Finset α → ℝ) :
    ip a x = ip a (restr G t x) := by
  unfold ip restr
  refine sum_congr rfl fun S _ => ?_
  by_cases ha : a S = 0
  · simp [ha]
  · rw [ite_eq_left (h S ha)]

lemma Up_restr (G : Finset α) (t : ℕ) (f : Finset α → ℝ) :
    Up G (restr G t f) = restr G (t + 1) (Up G f) := by
  funext S
  unfold Up restr
  by_cases hS : S ⊆ G ∧ S.card = t + 1
  · rw [ite_eq_left hS]
    refine sum_congr rfl fun x hx => ?_
    rw [mem_inter] at hx
    rw [ite_eq_left ⟨(erase_subset x S).trans hS.1, by rw [card_erase_of_mem hx.1, hS.2]; rfl⟩]
  · rw [ite_eq_right hS]
    refine sum_eq_zero fun x hx => ?_
    rw [mem_inter] at hx
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    apply hS
    refine ⟨?_, ?_⟩
    · rw [← insert_erase hx.1]; exact insert_subset hx.2 h1
    · rw [← card_erase_add_one hx.1, h2]

lemma Dn_restr (G : Finset α) (t : ℕ) (g : Finset α → ℝ) :
    Dn G (restr G (t + 1) g) = restr G t (Dn G g) := by
  funext S
  unfold Dn restr
  by_cases hS : S ⊆ G ∧ S.card = t
  · rw [ite_eq_left hS]
    refine sum_congr rfl fun y hy => ?_
    rw [mem_sdiff] at hy
    rw [ite_eq_left ⟨insert_subset hy.1 hS.1, by rw [card_insert_of_notMem hy.2, hS.2]⟩]
  · rw [ite_eq_right hS]
    refine sum_eq_zero fun y hy => ?_
    rw [mem_sdiff] at hy
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    apply hS
    refine ⟨(subset_insert y S).trans h1, ?_⟩
    rw [card_insert_of_notMem hy.2] at h2; omega

/-- Norm identity: for `f` on level `t`, `‖Up f‖² = ‖Dn f‖² + (#G - 2t) ‖f‖²`. -/
lemma qU [Fintype α] {G : Finset α} {t : ℕ} {f : Finset α → ℝ} (hf : Lev G t f) :
    ip (Up G f) (Up G f) = ip (Dn G f) (Dn G f) + ((G.card : ℝ) - 2 * t) * ip f f := by
  have h := ip_Up G (Dn G f) f
  rw [ip_Up, ← h, ip_comm (Up G (Dn G f)) f]
  unfold ip
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun S _ => ?_
  have hc := comm_apply G f S
  by_cases h0 : f S = 0
  · simp [h0]
  · obtain ⟨hSG, hSt⟩ := hf S h0
    have e1 : (S ∩ G).card = t := by rw [inter_eq_left.2 hSG, hSt]
    have e2 : ((G \ S).card : ℝ) = G.card - t := by
      have := card_sdiff_add_card_eq_card hSG
      rw [← hSt]; rw [← this]; push_cast; ring
    rw [e1, e2] at hc
    have : Dn G (Up G f) S = Up G (Dn G f) S + ((G.card : ℝ) - t - t) * f S := by linarith
    rw [this]; ring

/-- `Up` is injective on level `t` when `#G > 2t`. -/
lemma Up_inj [Fintype α] {G : Finset α} {t : ℕ} {f : Finset α → ℝ} (hf : Lev G t f)
    (hpos : 0 < (G.card : ℝ) - 2 * t) (hU : Up G f = 0) : f = 0 := by
  have h := qU hf
  rw [hU] at h
  have h0 : ip (0 : Finset α → ℝ) 0 = 0 := by simp [ip]
  rw [h0] at h
  have h1 := ip_self_nonneg (Dn G f)
  have h2 := ip_self_nonneg f
  have : ip f f = 0 := by nlinarith
  exact eq_zero_of_ip_self f this

/-- On level `t` of a ground set with `2t - 1` points, `ker Up ⊆ ker Dn²`. -/
lemma kerUp_kerDD [Fintype α] {G : Finset α} {t : ℕ} {f : Finset α → ℝ} (hf : Lev G t f) (ht : 1 ≤ t)
    (hG : (G.card : ℝ) = 2 * t - 1) (hU : Up G f = 0) : Dn G (Dn G f) = 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hDf : Lev G s (Dn G f) := Lev_Dn hf
  have h0 : ip (0 : Finset α → ℝ) 0 = 0 := by simp [ip]
  have e1 := qU hf
  rw [hU, h0, hG] at e1
  have hUD : Up G (Dn G f) = f := by
    funext S
    have hc := comm_apply G f S
    have hz : Dn G (Up G f) S = 0 := by rw [hU]; simp [Dn]
    by_cases h0 : f S = 0
    · rw [h0] at hc ⊢; linarith
    · obtain ⟨hSG, hSt⟩ := hf S h0
      have e1 : (S ∩ G).card = s + 1 := by rw [inter_eq_left.2 hSG, hSt]
      have e2 : ((G \ S).card : ℝ) = G.card - (s + 1) := by
        have := card_sdiff_add_card_eq_card hSG
        rw [← this, hSt]; push_cast; ring
      rw [e1, e2, hG, hz] at hc
      push_cast at hc
      linarith
  have e2 := qU hDf
  rw [hUD, hG] at e2
  push_cast at e1 e2
  have h3 : ip (Dn G (Dn G f)) (Dn G (Dn G f)) = 0 := by linarith
  exact eq_zero_of_ip_self _ h3

lemma Up_add (G : Finset α) (f g : Finset α → ℝ) : Up G (f + g) = Up G f + Up G g := by
  funext S; simp [Up, sum_add_distrib]

lemma Up_smul (G : Finset α) (c : ℝ) (f : Finset α → ℝ) : Up G (c • f) = c • Up G f := by
  funext S; simp [Up, mul_sum]

lemma Dn_add (G : Finset α) (f g : Finset α → ℝ) : Dn G (f + g) = Dn G f + Dn G g := by
  funext S; simp [Dn, sum_add_distrib]

lemma Dn_smul (G : Finset α) (c : ℝ) (f : Finset α → ℝ) : Dn G (c • f) = c • Dn G f := by
  funext S; simp [Dn, mul_sum]

/-- Orthogonal complement of `ker Up` is the range of `Dn` (finite-dimensional linear algebra). -/
lemma exists_Dn_eq [Fintype α] (G : Finset α) (a : Finset α → ℝ) (ha : ∀ x, Up G x = 0 → ip a x = 0) :
    ∃ g, Dn G g = a := by
  let UL : EuclideanSpace ℝ (Finset α) →ₗ[ℝ] EuclideanSpace ℝ (Finset α) :=
    { toFun := fun v => WithLp.toLp 2 (Up G (WithLp.ofLp v))
      map_add' := by
        intro v w; rw [WithLp.ofLp_add, Up_add, WithLp.toLp_add]
      map_smul' := by
        intro c v; rw [WithLp.ofLp_smul, Up_smul, WithLp.toLp_smul]; rfl }
  let DL : EuclideanSpace ℝ (Finset α) →ₗ[ℝ] EuclideanSpace ℝ (Finset α) :=
    { toFun := fun v => WithLp.toLp 2 (Dn G (WithLp.ofLp v))
      map_add' := by
        intro v w; rw [WithLp.ofLp_add, Dn_add, WithLp.toLp_add]
      map_smul' := by
        intro c v; rw [WithLp.ofLp_smul, Dn_smul, WithLp.toLp_smul]; rfl }
  have hadj : DL = UL.adjoint := by
    rw [LinearMap.eq_adjoint_iff]
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial]
    have := ip_Up G (WithLp.ofLp y) (WithLp.ofLp x)
    unfold ip at this
    simp only [UL, DL, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
    rw [this]
  have hmem : WithLp.toLp 2 a ∈ (LinearMap.ker UL)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have hu' : Up G (WithLp.ofLp u) = 0 := by
      have := congrArg WithLp.ofLp hu
      simpa [UL] using this
    have := ha _ hu'
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial]
    unfold ip at this
    exact this
  rw [LinearMap.orthogonal_ker, ← hadj] at hmem
  obtain ⟨v, hv⟩ := hmem
  refine ⟨WithLp.ofLp v, ?_⟩
  have := congrArg WithLp.ofLp hv
  simpa [DL] using this


/-- The link of `β` at `i`: `T ↦ β (T ∪ {i})` on sets avoiding `i`. -/
def lk (i : α) (β : Finset α → ℝ) (T : Finset α) : ℝ :=
  if i ∈ T then 0 else β (insert i T)

/-- The deletion of `β` at `i`: `β` on sets avoiding `i`. -/
def dl (i : α) (β : Finset α → ℝ) (S : Finset α) : ℝ :=
  if i ∈ S then 0 else β S

lemma ip_lk [Fintype α] (i : α) (β : Finset α → ℝ) :
    ip (lk i β) (lk i β) = ∑ S, if i ∈ S then β S * β S else 0 := by
  rw [← sum_avoid_eq_sum_contain i (fun S => β S * β S)]
  unfold ip lk
  refine sum_congr rfl fun T _ => ?_
  split_ifs <;> simp

lemma ip_dl [Fintype α] (i : α) (β : Finset α → ℝ) :
    ip (dl i β) (dl i β) = ∑ S, if i ∈ S then 0 else β S * β S := by
  unfold ip dl
  refine sum_congr rfl fun T _ => ?_
  split_ifs <;> simp

/-- The linear-algebra core of the new step: with `#G = 2k`, a function `β` on `(k+1)`-sets
with `Up β = 0`, and functions `γ i` on `(k-1)`-sets and `δ i` on `(k-2)`-sets of `G \ {i}` with
`β (T ∪ {i}) + Up (γ i) T = 0` and `γ i R + Up (δ i) R = 0`, everything vanishes. -/
theorem froberg_core [Fintype α] (G : Finset α) (k : ℕ) (hG : G.card = 2 * k)
    (β : Finset α → ℝ) (γ δ : α → Finset α → ℝ)
    (hβ : Lev G (k + 1) β)
    (hγ : ∀ i R, γ i R ≠ 0 → R ⊆ G.erase i ∧ R.card + 1 = k)
    (hδ : ∀ i R, δ i R ≠ 0 → R ⊆ G.erase i ∧ R.card + 2 = k)
    (h1 : ∀ S, S ⊆ G → S.card = k + 2 → Up G β S = 0)
    (h2 : ∀ i ∈ G, ∀ T, T ⊆ G.erase i → T.card = k →
      β (insert i T) + Up (G.erase i) (γ i) T = 0)
    (h3 : ∀ i ∈ G, ∀ R, R ⊆ G.erase i → R.card + 1 = k →
      γ i R + Up (G.erase i) (δ i) R = 0) :
    β = 0 ∧ ∀ i ∈ G, γ i = 0 ∧ δ i = 0 := by
  have hUβ : Up G β = 0 := by
    funext S
    by_contra hne
    obtain ⟨hS1, hS2⟩ := Lev_Up hβ S hne
    exact hne (h1 S hS1 hS2)
  have hk : ∀ i ∈ G, 1 ≤ k := by
    intro i hi
    have := card_pos.2 ⟨i, hi⟩
    omega
  have hGi : ∀ i ∈ G, ((G.erase i).card : ℝ) = 2 * k - 1 := by
    intro i hi
    have h1k := hk i hi
    rw [card_erase_of_mem hi, hG, Nat.cast_sub (by omega)]
    push_cast; ring
  -- Up on the link is minus the deletion.
  have hUa : ∀ i ∈ G, Up (G.erase i) (lk i β) = fun S => -(dl i β S) := by
    intro i hi
    funext S
    unfold Up lk dl
    by_cases hiS : i ∈ S
    · rw [ite_eq_left hiS, neg_zero]
      refine sum_eq_zero fun x hx => ?_
      have hxi : x ≠ i := (mem_erase.1 (mem_inter.1 hx).2).1
      rw [ite_eq_left (mem_erase.2 ⟨Ne.symm hxi, hiS⟩)]
    · rw [ite_eq_right hiS]
      have hz := congrFun hUβ (insert i S)
      simp only [Up, Pi.zero_apply] at hz
      rw [insert_inter_of_mem hi, sum_insert (fun h => hiS (mem_inter.1 h).1),
        erase_insert hiS] at hz
      have hSG : S ∩ G.erase i = S ∩ G := by
        ext x
        simp only [mem_inter, mem_erase]
        constructor
        · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨h1, fun h => hiS (h ▸ h1), h3⟩
      rw [hSG]
      have : ∑ x ∈ S ∩ G, (if i ∈ S.erase x then 0 else β (insert i (S.erase x))) =
          ∑ x ∈ S ∩ G, β ((insert i S).erase x) := by
        refine sum_congr rfl fun x hx => ?_
        have hxi : i ≠ x := fun h => hiS (h ▸ (mem_inter.1 hx).1)
        rw [ite_eq_right (fun h => hiS (mem_of_mem_erase h)), erase_insert_of_ne hxi]
      rw [this]
      linarith
  -- Key per-point inequality.
  have key : ∀ i ∈ G, 3 * ip (lk i β) (lk i β) ≤ ip (dl i β) (dl i β) := by
    intro i hi
    have hk1 := hk i hi
    have haLev : Lev (G.erase i) k (lk i β) := by
      intro T hT
      unfold lk at hT
      split_ifs at hT with hiT
      · exact absurd rfl hT
      · obtain ⟨h1', h2'⟩ := hβ _ hT
        refine ⟨fun x hx => mem_erase.2 ⟨fun h => hiT (h ▸ hx), h1' (mem_insert_of_mem hx)⟩, ?_⟩
        rw [card_insert_of_notMem hiT] at h2'
        omega
    have hUUlev : Lev (G.erase i) k (Up (G.erase i) (Up (G.erase i) (δ i))) := by
      by_cases hk2 : 2 ≤ k
      · have hl : Lev (G.erase i) (k - 2) (δ i) := fun R hR =>
          ⟨(hδ i R hR).1, by have := (hδ i R hR).2; omega⟩
        have := Lev_Up (Lev_Up hl)
        rwa [show k - 2 + 1 + 1 = k by omega] at this
      · have h0 : δ i = 0 := funext fun R => by
          by_contra hR
          have := (hδ i R hR).2
          omega
        intro S hS
        exfalso; apply hS
        rw [h0]; simp [Up]
    have hUUδ : lk i β = Up (G.erase i) (Up (G.erase i) (δ i)) := by
      funext T
      by_cases hT : T ⊆ G.erase i ∧ T.card = k
      · have hiT : i ∉ T := fun h => (mem_erase.1 (hT.1 h)).1 rfl
        have e := h2 i hi T hT.1 hT.2
        have e2 : Up (G.erase i) (γ i) T = -Up (G.erase i) (Up (G.erase i) (δ i)) T := by
          rw [Up, Up, ← sum_neg_distrib]
          refine sum_congr rfl fun x hx => ?_
          have hx' := mem_inter.1 hx
          have := h3 i hi (T.erase x) ((erase_subset x T).trans hT.1)
            (by rw [card_erase_of_mem hx'.1, hT.2]; omega)
          linarith
        unfold lk
        rw [ite_eq_right hiT]
        linarith
      · have ha0 : lk i β T = 0 := by
          by_contra hne; exact hT (haLev T hne)
        have hb0 : Up (G.erase i) (Up (G.erase i) (δ i)) T = 0 := by
          by_contra hne; exact hT (hUUlev T hne)
        rw [ha0, hb0]
    have hperp : ∀ x, Up (G.erase i) x = 0 → ip (lk i β) x = 0 := by
      intro x hx
      rw [ip_restr haLev x]
      have hyLev := Lev_restr (G.erase i) k x
      have hUy : Up (G.erase i) (restr (G.erase i) k x) = 0 := by
        rw [Up_restr, hx]
        funext S; simp [restr]
      have hDD := kerUp_kerDD hyLev hk1 (hGi i hi) hUy
      rw [hUUδ, ip_Up, ip_Up, hDD]
      simp [ip]
    obtain ⟨g, hg⟩ := exists_Dn_eq (G.erase i) (lk i β) hperp
    have hg' : Dn (G.erase i) (restr (G.erase i) (k + 1) g) = lk i β := by
      rw [Dn_restr, hg, restr_of_Lev haLev]
    have hg'Lev := Lev_restr (G.erase i) (k + 1) g
    set g' := restr (G.erase i) (k + 1) g
    set u := Up (G.erase i) (lk i β)
    have eA : ip (lk i β) (lk i β) = ip g' u := by
      calc ip (lk i β) (lk i β) = ip (Dn (G.erase i) g') (lk i β) := by rw [hg']
        _ = ip (lk i β) (Dn (G.erase i) g') := ip_comm _ _
        _ = ip u g' := (ip_Up _ _ _).symm
        _ = ip g' u := ip_comm _ _
    have eQ := qU hg'Lev
    rw [hg', hGi i hi] at eQ
    push_cast at eQ
    have hCS : (ip g' u) ^ 2 ≤ ip g' g' * ip u u := by
      have := sum_mul_sq_le_sq_mul_sq univ g' u
      unfold ip
      simpa only [sq] using this
    have hu : ip u u = ip (dl i β) (dl i β) := by
      simp only [u, hUa i hi, ip, neg_mul_neg]
    rw [← hu]
    rw [← eA] at hCS
    have hA := ip_self_nonneg (lk i β)
    have hB := ip_self_nonneg g'
    have hC := ip_self_nonneg u
    have hU2 := ip_self_nonneg (Up (G.erase i) g')
    have h3B : 3 * ip g' g' ≤ ip (lk i β) (lk i β) := by linarith
    have hprod : ip (lk i β) (lk i β) * (3 * ip (lk i β) (lk i β) - ip u u) ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_right h3B hC]
    by_contra hcon
    rw [not_le] at hcon
    have hApos : 0 < ip (lk i β) (lk i β) := by
      by_contra h0
      rw [not_lt] at h0
      have : ip (lk i β) (lk i β) = 0 := le_antisymm h0 hA
      rw [this] at hcon; linarith
    nlinarith
  -- Sum the inequality over `i ∈ G`.
  have hsa : ∑ i ∈ G, ip (lk i β) (lk i β) = ((k : ℝ) + 1) * ip β β := by
    simp_rw [ip_lk]
    rw [sum_comm]
    unfold ip
    rw [mul_sum]
    refine sum_congr rfl fun S _ => ?_
    by_cases h0 : β S = 0
    · simp [h0]
    · obtain ⟨hS1, hS2⟩ := hβ S h0
      rw [sum_ite_mem, sum_const, inter_eq_right.2 hS1, hS2, nsmul_eq_mul]
      push_cast; ring
  have hsb : ∑ i ∈ G, ip (dl i β) (dl i β) = ((k : ℝ) - 1) * ip β β := by
    simp_rw [ip_dl]
    rw [sum_comm]
    unfold ip
    rw [mul_sum]
    refine sum_congr rfl fun S _ => ?_
    by_cases h0 : β S = 0
    · simp [h0]
    · obtain ⟨hS1, hS2⟩ := hβ S h0
      rw [sum_ite, sum_const_zero, zero_add, sum_const, filter_notMem_eq_sdiff, nsmul_eq_mul]
      have := card_sdiff_add_card_eq_card hS1
      rw [hS2, hG] at this
      have e : ((G \ S).card : ℝ) = (k : ℝ) - 1 := by
        have : ((G \ S).card : ℝ) + (k + 1) = 2 * k := by exact_mod_cast this
        linarith
      rw [e]
  have hsum : 3 * (((k : ℝ) + 1) * ip β β) ≤ ((k : ℝ) - 1) * ip β β := by
    rw [← hsa, ← hsb, mul_sum]
    exact sum_le_sum key
  have hN := ip_self_nonneg β
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hβ0 : β = 0 := by
    apply eq_zero_of_ip_self
    nlinarith
  refine ⟨hβ0, fun i hi => ?_⟩
  have hk1 := hk i hi
  have hγ0 : γ i = 0 := by
    have hl : Lev (G.erase i) (k - 1) (γ i) := fun R hR =>
      ⟨(hγ i R hR).1, by have := (hγ i R hR).2; omega⟩
    have hU : Up (G.erase i) (γ i) = 0 := by
      funext T
      by_contra hne
      obtain ⟨hT1, hT2⟩ := Lev_Up hl T hne
      have e := h2 i hi T hT1 (by omega)
      rw [hβ0] at e
      simp only [Pi.zero_apply, zero_add] at e
      exact hne e
    apply Up_inj hl _ hU
    rw [hGi i hi, Nat.cast_sub hk1]
    push_cast; linarith
  refine ⟨hγ0, ?_⟩
  by_cases hk2 : 2 ≤ k
  · have hl : Lev (G.erase i) (k - 2) (δ i) := fun R hR =>
      ⟨(hδ i R hR).1, by have := (hδ i R hR).2; omega⟩
    have hU : Up (G.erase i) (δ i) = 0 := by
      funext T
      by_contra hne
      obtain ⟨hT1, hT2⟩ := Lev_Up hl T hne
      have e := h3 i hi T hT1 (by omega)
      rw [hγ0] at e
      simp only [Pi.zero_apply, zero_add] at e
      exact hne e
    apply Up_inj hl _ hU
    rw [hGi i hi, Nat.cast_sub hk2]
    push_cast; linarith
  · funext R
    by_contra hR
    have := (hδ i R hR).2
    omega

/-- Complex-valued form of `froberg_core` (apply it to real and imaginary parts). -/
theorem froberg_core_complex [Fintype α] (G : Finset α) (k : ℕ) (hG : G.card = 2 * k)
    (β : Finset α → ℂ) (γ δ : α → Finset α → ℂ)
    (hβ : ∀ S, β S ≠ 0 → S ⊆ G ∧ S.card = k + 1)
    (hγ : ∀ i R, γ i R ≠ 0 → R ⊆ G.erase i ∧ R.card + 1 = k)
    (hδ : ∀ i R, δ i R ≠ 0 → R ⊆ G.erase i ∧ R.card + 2 = k)
    (h1 : ∀ S, S ⊆ G → S.card = k + 2 → ∑ x ∈ S ∩ G, β (S.erase x) = 0)
    (h2 : ∀ i ∈ G, ∀ T, T ⊆ G.erase i → T.card = k →
      β (insert i T) + ∑ x ∈ T ∩ G.erase i, γ i (T.erase x) = 0)
    (h3 : ∀ i ∈ G, ∀ R, R ⊆ G.erase i → R.card + 1 = k →
      γ i R + ∑ x ∈ R ∩ G.erase i, δ i (R.erase x) = 0) :
    β = 0 ∧ ∀ i ∈ G, γ i = 0 ∧ δ i = 0 := by
  have part : ∀ φ : ℂ →+ ℝ, (fun S => φ (β S)) = 0 ∧
      ∀ i ∈ G, (fun R => φ (γ i R)) = 0 ∧ (fun R => φ (δ i R)) = 0 := by
    intro φ
    apply froberg_core G k hG (fun S => φ (β S)) (fun i R => φ (γ i R)) (fun i R => φ (δ i R))
    · intro S hS
      apply hβ S
      intro h0; apply hS; simp [h0]
    · intro i R hR
      apply hγ i R
      intro h0; apply hR; simp [h0]
    · intro i R hR
      apply hδ i R
      intro h0; apply hR; simp [h0]
    · intro S hS1 hS2
      simp only [Up]
      rw [← map_sum, h1 S hS1 hS2, map_zero]
    · intro i hi T hT1 hT2
      simp only [Up]
      rw [← map_sum, ← map_add, h2 i hi T hT1 hT2, map_zero]
    · intro i hi R hR1 hR2
      simp only [Up]
      rw [← map_sum, ← map_add, h3 i hi R hR1 hR2, map_zero]
  obtain ⟨hr1, hr2⟩ := part Complex.reAddGroupHom
  obtain ⟨hi1, hi2⟩ := part Complex.imAddGroupHom
  have ext0 : ∀ z : ℂ, Complex.reAddGroupHom z = 0 → Complex.imAddGroupHom z = 0 → z = 0 :=
    fun z h1 h2 => Complex.ext h1 h2
  refine ⟨funext fun S => ext0 _ (congrFun hr1 S) (congrFun hi1 S), fun i hi => ⟨?_, ?_⟩⟩
  · exact funext fun R => ext0 _ (congrFun (hr2 i hi).1 R) (congrFun (hi2 i hi).1 R)
  · exact funext fun R => ext0 _ (congrFun (hr2 i hi).2 R) (congrFun (hi2 i hi).2 R)

/-!
Part 3. The ring `T_{n,2,2} = ℂ[x_σ] / (x_i² : i)²`. Its ideal is the monomial ideal spanned by
`x_i² x_j²` (`i = j` allowed). A monomial `m` is `bad` when it lies in that ideal.
-/

open MvPolynomial

section Poly

variable {σ : Type*} [DecidableEq σ]

/-- The squarefree exponent vector of a set. -/
noncomputable def ind (S : Finset σ) : σ →₀ ℕ :=
  ∑ x ∈ S, Finsupp.single x 1

lemma ind_apply (S : Finset σ) (y : σ) : ind S y = if y ∈ S then 1 else 0 := by
  simp [ind, Finsupp.finsetSum_apply, Finsupp.single_apply]

omit [DecidableEq σ] in
lemma degree_ind (S : Finset σ) : (ind S).degree = S.card := by
  simp [ind, map_sum, Finsupp.degree_single]

/-- Monomials of the ideal `(x_i²)²`. -/
def bad (m : σ →₀ ℕ) : Prop :=
  ∃ i j, Finsupp.single i 2 + Finsupp.single j 2 ≤ m

lemma bad_of_four {m : σ →₀ ℕ} {y : σ} (hy : 4 ≤ m y) : bad m := by
  refine ⟨y, y, ?_⟩
  rw [Finsupp.le_def]
  intro z
  by_cases hz : z = y
  · subst hz; simp; omega
  · simp [Ne.symm hz]

lemma bad_of_two {m : σ →₀ ℕ} {y z : σ} (hyz : y ≠ z) (hy : 2 ≤ m y) (hz : 2 ≤ m z) :
    bad m := by
  refine ⟨y, z, ?_⟩
  rw [Finsupp.le_def]
  intro w
  by_cases hw : w = y
  · subst hw; simp [hyz]; exact hy
  · by_cases hw' : w = z
    · subst hw'; simp [Ne.symm hyz]; exact hz
    · simp [Ne.symm hw, Ne.symm hw']

lemma not_bad {m : σ →₀ ℕ} (h3 : ∀ y, m y ≤ 3)
    (h1 : ∀ y z, y ≠ z → m y ≤ 1 ∨ m z ≤ 1) : ¬ bad m := by
  rintro ⟨a, b, hab⟩
  rw [Finsupp.le_def] at hab
  by_cases h : a = b
  · subst h
    have := hab a
    have := h3 a
    simp at *
    omega
  · have ha := hab a
    have hb := hab b
    simp [h, Ne.symm h] at ha hb
    rcases h1 a b h with h' | h' <;> omega

lemma not_bad_ind (S : Finset σ) : ¬ bad (ind S) := by
  apply not_bad
  · intro y; rw [ind_apply]; split_ifs <;> omega
  · intro y z _; left; rw [ind_apply]; split_ifs <;> omega

lemma single_add_ind_apply (i : σ) (c : ℕ) (T : Finset σ) (hiT : i ∉ T) (y : σ) :
    (Finsupp.single i c + ind T) y = if y = i then c else (if y ∈ T then 1 else 0) := by
  rw [Finsupp.add_apply, ind_apply, Finsupp.single_apply]
  by_cases hy : y = i
  · subst hy; simp [hiT]
  · simp [Ne.symm hy, hy]

lemma not_bad_single_add_ind (i : σ) (c : ℕ) (hc : c ≤ 3) (T : Finset σ) (hiT : i ∉ T) :
    ¬ bad (Finsupp.single i c + ind T) := by
  apply not_bad
  · intro y; rw [single_add_ind_apply i c T hiT]; split_ifs <;> omega
  · intro y z hyz
    rw [single_add_ind_apply i c T hiT, single_add_ind_apply i c T hiT]
    by_cases hy : y = i
    · right; rw [ite_eq_right (fun h => hyz (hy.trans h.symm))]; split_ifs <;> omega
    · left; rw [ite_eq_right hy]; split_ifs <;> omega

lemma support_ind (S : Finset σ) : (ind S).support = S := by
  ext y; simp [Finsupp.mem_support_iff, ind_apply]

lemma support_single_add_ind (i : σ) (c : ℕ) (hc : c ≠ 0) (T : Finset σ) (hiT : i ∉ T) :
    (Finsupp.single i c + ind T).support = insert i T := by
  ext y
  rw [Finsupp.mem_support_iff, single_add_ind_apply i c T hiT, mem_insert]
  by_cases hy : y = i
  · simp [hy, hc]
  · simp [hy]

lemma ind_sub_single (S : Finset σ) (x : σ) (hx : x ∈ S) :
    ind S - Finsupp.single x 1 = ind (S.erase x) := by
  ext y
  rw [Finsupp.coe_tsub, Pi.sub_apply, ind_apply, ind_apply, Finsupp.single_apply]
  by_cases hy : y = x
  · subst hy; simp [hx]
  · simp [Ne.symm hy, hy, mem_erase]

lemma single_add_ind_sub_self (i : σ) (c : ℕ) (T : Finset σ) (hiT : i ∉ T) :
    Finsupp.single i (c + 1) + ind T - Finsupp.single i 1 = Finsupp.single i c + ind T := by
  ext y
  rw [Finsupp.coe_tsub, Pi.sub_apply, single_add_ind_apply i _ T hiT,
    single_add_ind_apply i _ T hiT, Finsupp.single_apply]
  by_cases hy : y = i
  · subst hy; simp
  · simp [Ne.symm hy, hy]

lemma single_add_ind_sub_other (i : σ) (c : ℕ) (T : Finset σ) (hiT : i ∉ T) (x : σ) (hx : x ∈ T) :
    Finsupp.single i c + ind T - Finsupp.single x 1 = Finsupp.single i c + ind (T.erase x) := by
  have hxi : x ≠ i := fun h => hiT (h ▸ hx)
  have hiT' : i ∉ T.erase x := fun h => hiT (mem_of_mem_erase h)
  ext y
  rw [Finsupp.coe_tsub, Pi.sub_apply, single_add_ind_apply i _ T hiT,
    single_add_ind_apply i _ _ hiT', Finsupp.single_apply]
  by_cases hy : y = i
  · subst hy; simp [hxi]
  · by_cases hyx : y = x
    · subst hyx; simp [hy, hx]
    · simp [hy, hyx, Ne.symm hyx, mem_erase]

lemma single_one_add_ind (i : σ) (T : Finset σ) (hiT : i ∉ T) :
    Finsupp.single i 1 + ind T = ind (insert i T) := by
  ext y
  rw [single_add_ind_apply i _ T hiT, ind_apply]
  by_cases hy : y = i
  · simp [hy]
  · simp [hy, mem_insert]

variable {R : Type*} [CommSemiring R]

omit [DecidableEq σ] in
/-- `(x_i² : i)²` is the monomial ideal of the exponents `2e_i + 2e_j`. -/
lemma sqIdeal_eq :
    (Ideal.span (Set.range fun i : σ => (X i : MvPolynomial σ R) ^ 2)) ^ 2 =
      Ideal.span ((fun s => monomial s (1 : R)) ''
        {m | ∃ i j, m = Finsupp.single i 2 + Finsupp.single j 2}) := by
  rw [sq, Ideal.span_mul_span]
  congr 1
  ext q
  simp only [Set.mem_mul, Set.mem_range, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact ⟨_, ⟨i, j, rfl⟩, by rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul]⟩
  · rintro ⟨_, ⟨i, j, rfl⟩, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, by
      rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul]⟩

omit [DecidableEq σ] in
lemma mem_sqIdeal {q : MvPolynomial σ R} :
    q ∈ (Ideal.span (Set.range fun i : σ => (X i : MvPolynomial σ R) ^ 2)) ^ 2 ↔
      ∀ m, q.coeff m ≠ 0 → bad m := by
  rw [sqIdeal_eq, mem_ideal_span_monomial_image]
  simp only [mem_support_iff, Set.mem_ofPred_eq]
  constructor
  · intro h m hm
    obtain ⟨_, ⟨i, j, rfl⟩, hle⟩ := h m hm
    exact ⟨i, j, hle⟩
  · intro h m hm
    obtain ⟨i, j, hle⟩ := h m hm
    exact ⟨_, ⟨i, j, rfl⟩, hle⟩

lemma coeff_ell_mul [Fintype σ] (p : MvPolynomial σ R) (m : σ →₀ ℕ) :
    ((∑ i, X i) * p).coeff m = ∑ i ∈ m.support, p.coeff (m - Finsupp.single i 1) := by
  rw [sum_mul, coeff_sum]
  simp_rw [coeff_X_mul']
  rw [sum_ite_mem, univ_inter]

/-- **New step of Problem H.** Let `#σ = 2k` and `R = ℂ[x_σ] / (x_i² : i)²`. Multiplication by
`ℓ = ∑ x_i` is injective from `R_{k+1}` to `R_{k+2}`: a form `p` of degree `k+1` with
`ℓ p ∈ (x_i²)²` already lies in `(x_i²)²`. -/
theorem froberg_H_mul_ell_injective [Fintype σ] (k : ℕ) (hσ : Fintype.card σ = 2 * k)
    (p : MvPolynomial σ ℂ) (hp : p.IsHomogeneous (k + 1))
    (h : (∑ i, X i) * p ∈ (Ideal.span (Set.range fun i : σ => (X i : MvPolynomial σ ℂ) ^ 2)) ^ 2) :
    p ∈ (Ideal.span (Set.range fun i : σ => (X i : MvPolynomial σ ℂ) ^ 2)) ^ 2 := by
  rw [mem_sqIdeal] at h ⊢
  have hc : ∀ m, ¬ bad m → ∑ i ∈ m.support, p.coeff (m - Finsupp.single i 1) = 0 := by
    intro m hm
    rw [← coeff_ell_mul]
    by_contra hne
    exact hm (h m hne)
  have hsub : ∀ (i : σ) (R : Finset σ), i ∉ R → R ⊆ univ.erase i := fun i R hiR x hx =>
    mem_erase.2 ⟨fun h => hiR (h ▸ hx), mem_univ x⟩
  have hnot : ∀ (i : σ) (R : Finset σ), R ⊆ univ.erase i → i ∉ R := fun i R hR h =>
    (mem_erase.1 (hR h)).1 rfl
  obtain ⟨hβ0, hγδ0⟩ := froberg_core_complex (univ : Finset σ) k (by rw [card_univ, hσ])
    (fun S => if S.card = k + 1 then p.coeff (ind S) else 0)
    (fun i R => if i ∉ R ∧ R.card + 1 = k then p.coeff (Finsupp.single i 2 + ind R) else 0)
    (fun i R => if i ∉ R ∧ R.card + 2 = k then p.coeff (Finsupp.single i 3 + ind R) else 0)
    (by
      intro S hS
      split_ifs at hS with h1
      · exact ⟨subset_univ S, h1⟩
      · exact absurd rfl hS)
    (by
      intro i R hR
      split_ifs at hR with h1
      · exact ⟨hsub i R h1.1, h1.2⟩
      · exact absurd rfl hR)
    (by
      intro i R hR
      split_ifs at hR with h1
      · exact ⟨hsub i R h1.1, h1.2⟩
      · exact absurd rfl hR)
    (by
      intro S _ hS2
      have e := hc (ind S) (not_bad_ind S)
      rw [support_ind] at e
      rw [inter_univ, ← e]
      refine sum_congr rfl fun x hx => ?_
      rw [ite_eq_left (by rw [card_erase_of_mem hx, hS2]; rfl), ind_sub_single S x hx])
    (by
      intro i _ T hT hT2
      have hiT := hnot i T hT
      have e := hc _ (not_bad_single_add_ind i 2 (by norm_num) T hiT)
      rw [support_single_add_ind i 2 (by norm_num) T hiT, sum_insert hiT,
        single_add_ind_sub_self i 1 T hiT, single_one_add_ind i T hiT] at e
      rw [inter_eq_left.2 hT, ite_eq_left (by rw [card_insert_of_notMem hiT, hT2]), ← e]
      congr 1
      refine sum_congr rfl fun x hx => ?_
      rw [ite_eq_left ⟨fun h => hiT (mem_of_mem_erase h), by
        rw [card_erase_of_mem hx, hT2]; have := card_pos.2 ⟨x, hx⟩; omega⟩,
        single_add_ind_sub_other i 2 T hiT x hx])
    (by
      intro i _ R hR hR2
      have hiR := hnot i R hR
      have e := hc _ (not_bad_single_add_ind i 3 (by norm_num) R hiR)
      rw [support_single_add_ind i 3 (by norm_num) R hiR, sum_insert hiR,
        single_add_ind_sub_self i 2 R hiR] at e
      rw [inter_eq_left.2 hR, ite_eq_left ⟨hiR, hR2⟩, ← e]
      congr 1
      refine sum_congr rfl fun x hx => ?_
      rw [ite_eq_left ⟨fun h => hiR (mem_of_mem_erase h), by
        rw [card_erase_of_mem hx]; have := card_pos.2 ⟨x, hx⟩; omega⟩,
        single_add_ind_sub_other i 3 R hiR x hx])
  intro m hm
  by_contra hgood
  have hdeg : m.degree = k + 1 := by
    by_contra hd
    exact hm (hp.coeff_eq_zero hd)
  have h3 : ∀ y, m y ≤ 3 := fun y => by
    by_contra hy; exact hgood (bad_of_four (y := y) (by omega))
  by_cases hall : ∀ y, m y ≤ 1
  · have hm_eq : m = ind m.support := by
      ext y
      rw [ind_apply]
      have := hall y
      by_cases hy : m y = 0
      · simp [hy]
      · have hy' : y ∈ m.support := Finsupp.mem_support_iff.2 hy
        simp only [hy', ite_true]
        omega
    have hcard : m.support.card = k + 1 := by
      rw [← hdeg, hm_eq, degree_ind, support_ind]
    have := congrFun hβ0 m.support
    simp only [hcard, ite_true, Pi.zero_apply] at this
    rw [← hm_eq] at this
    exact hm this
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hother : ∀ y, y ≠ i → m y ≤ 1 := fun y hy => by
      by_contra hy'; exact hgood (bad_of_two hy (by omega) (by omega))
    set R := m.support.erase i with hRdef
    have hiR : i ∉ R := fun h => (mem_erase.1 h).1 rfl
    have hm_eq : m = Finsupp.single i (m i) + ind R := by
      ext y
      rw [single_add_ind_apply i _ R hiR]
      by_cases hy : y = i
      · rw [ite_eq_left hy, hy]
      · rw [ite_eq_right hy]
        have := hother y hy
        by_cases h0 : m y = 0
        · have : y ∉ R := fun h => (mem_erase.1 h).2 |> Finsupp.mem_support_iff.1 |> (· h0)
          simp [h0, this]
        · have : y ∈ R := mem_erase.2 ⟨hy, Finsupp.mem_support_iff.2 h0⟩
          simp only [this, ite_true]
          omega
    have hdeg' : m i + R.card = k + 1 := by
      rw [← hdeg]
      conv_rhs => rw [hm_eq]
      rw [map_add, Finsupp.degree_single, degree_ind]
    have hR : R ⊆ univ.erase i := hsub i R hiR
    obtain ⟨hγ0, hδ0⟩ := hγδ0 i (mem_univ i)
    have hmi : m i = 2 ∨ m i = 3 := by have := h3 i; omega
    rcases hmi with h2 | h2
    · have := congrFun hγ0 R
      have hcond : i ∉ R ∧ R.card + 1 = k := ⟨hiR, by omega⟩
      simp only [Pi.zero_apply] at this
      rw [ite_eq_left hcond, ← h2, ← hm_eq] at this
      exact hm this
    · have := congrFun hδ0 R
      have hcond : i ∉ R ∧ R.card + 2 = k := ⟨hiR, by omega⟩
      simp only [Pi.zero_apply] at this
      rw [ite_eq_left hcond, ← h2, ← hm_eq] at this
      exact hm this

/-- The case `σ = Fin (2k)`, i.e. `T_{2k,2,2}`. -/
theorem froberg_H_even (k : ℕ) (p : MvPolynomial (Fin (2 * k)) ℂ) (hp : p.IsHomogeneous (k + 1))
    (h : (∑ i, X i) * p ∈
      (Ideal.span (Set.range fun i : Fin (2 * k) => (X i : MvPolynomial (Fin (2 * k)) ℂ) ^ 2)) ^ 2) :
    p ∈ (Ideal.span (Set.range fun i : Fin (2 * k) => (X i : MvPolynomial (Fin (2 * k)) ℂ) ^ 2)) ^ 2 :=
  froberg_H_mul_ell_injective k (Fintype.card_fin _) p hp h
