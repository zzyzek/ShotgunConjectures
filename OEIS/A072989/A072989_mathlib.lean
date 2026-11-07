import Mathlib

/-!
# OEIS A072989

A072989: numbers m > 0 such that the number of solutions of x^m ≡ 1 (mod m),
1 ≤ x ≤ m, differs from gcd(m, φ(m)).  Conjecture (OEIS wiki list):
"limit of a(n)/n is zero".

Checked here:
* `A072989_two_mod_four`: if m ≡ 2 (mod 4) and m = A·B with A, B coprime and
  both > 2, then m is in the sequence (4 divides the solution count, 4 does
  not divide gcd(m, φ(m))).
* `A072989_infinite`: the sequence is infinite (m = 6·5^(j+1)).
* `A072989_main`: a(n) ≥ n for n ≥ 1, so a(n)/n does not tend to 0
  (the conjecture as stated is false).

Not checked here: the density-one theorem a(n)/n → 1 (README, outside Lean).
-/

open Filter Topology

/-- Number of x with 1 ≤ x ≤ m and x^m ≡ 1 (mod m) (OEIS A072994). -/
def A072989N (m : ℕ) : ℕ := ((Finset.Icc 1 m).filter (fun x => x ^ m % m = 1 % m)).card

/-- Membership in A072989. -/
def A072989S (m : ℕ) : Prop := 0 < m ∧ A072989N m ≠ Nat.gcd m (Nat.totient m)

/-- The sequence, 1-indexed: a(1) = 20, a(2) = 30, … -/
noncomputable def A072989a (n : ℕ) : ℕ := Nat.nth A072989S (n - 1)

/-- Roots of x^m = 1 in a commutative monoid are units. -/
lemma A072989_card_roots_eq_units {R : Type*} [CommMonoid R] (m : ℕ) (hm : m ≠ 0) :
    Nat.card {z : R // z ^ m = 1} = Nat.card {u : Rˣ // u ^ m = 1} := by
  apply Nat.card_congr
  exact
    { toFun := fun z => ⟨Units.ofPowEqOne z.1 m z.2 hm, Units.pow_ofPowEqOne z.2 hm⟩
      invFun := fun u => ⟨(u.1 : R), by rw [← Units.val_pow_eq_pow_val, u.2]; rfl⟩
      left_inv := fun z => by ext; simp
      right_inv := fun u => by ext; simp }

/-- A072989N m counts the roots of z^m = 1 in ZMod m. -/
lemma A072989_N_eq_card (m : ℕ) (hm : 0 < m) :
    A072989N m = Nat.card {z : ZMod m // z ^ m = 1} := by
  have : NeZero m := ⟨hm.ne'⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, A072989N]
  refine Finset.card_bij (fun x _ => (x : ZMod m)) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have := (ZMod.natCast_eq_natCast_iff' (x ^ m) 1 m).2 hx.2
    simpa using this
  · intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx hy
    have h := (ZMod.natCast_eq_natCast_iff' x y m).1 hxy
    rcases lt_or_eq_of_le hx.1.2 with h1 | h1 <;>
      rcases lt_or_eq_of_le hy.1.2 with h2 | h2
    · rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h
    · subst h2; rw [Nat.mod_self, Nat.mod_eq_of_lt h1] at h; omega
    · subst h1; rw [Nat.mod_self, Nat.mod_eq_of_lt h2] at h; omega
    · omega
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    by_cases hv : z.val = 0
    · have h0 : z = 0 := (ZMod.val_eq_zero _).1 hv
      rw [h0, zero_pow hm.ne'] at hz
      have h1 : ((1 : ℕ) : ZMod m) = ((m : ℕ) : ZMod m) := by
        rw [ZMod.natCast_self, Nat.cast_one]; exact hz.symm
      have h2 := (ZMod.natCast_eq_natCast_iff' 1 m m).1 h1
      rw [Nat.mod_self] at h2
      refine ⟨m, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨hm, le_rfl⟩, ?_⟩
        rw [h2, Nat.pow_mod, Nat.mod_self, zero_pow hm.ne', Nat.zero_mod]
      · rw [h0, ZMod.natCast_self]
    · refine ⟨z.val, ?_, ZMod.natCast_zmod_val z⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.pos_of_ne_zero hv, (ZMod.val_lt z).le⟩, ?_⟩
      apply (ZMod.natCast_eq_natCast_iff' _ _ m).1
      simp [hz]

/-- For A > 2 and m even, the number of unit roots of u^m = 1 in ZMod A is even. -/
lemma A072989_two_dvd_card (A m : ℕ) (hA : 2 < A) (hm : Even m) :
    2 ∣ Nat.card {u : (ZMod A)ˣ // u ^ m = 1} := by
  have : Fact (2 < A) := ⟨hA⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup (ZMod A)ˣ := (powMonoidHom m).ker
  have hmem : (-1 : (ZMod A)ˣ) ∈ H := by
    simp [H, MonoidHom.mem_ker, hm.neg_one_pow]
  let x : H := ⟨-1, hmem⟩
  have hx2 : x ^ 2 = 1 := by ext; simp [x]
  have hx1 : x ≠ 1 := by
    intro h
    have := congrArg (fun y : H => ((y : (ZMod A)ˣ) : ZMod A)) h
    simp [x] at this
    exact ZMod.neg_one_ne_one this
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hcard : Nat.card H = Nat.card {u : (ZMod A)ˣ // u ^ m = 1} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun u => by simp [H, MonoidHom.mem_ker])
  rw [← hcard, ← hord]
  exact orderOf_dvd_natCard x

/-- Multiplicativity over a coprime splitting m = A·B. -/
lemma A072989_card_split (A B m : ℕ) (h : A.Coprime B) :
    Nat.card {u : (ZMod (A * B))ˣ // u ^ m = 1} =
      Nat.card {u : (ZMod A)ˣ // u ^ m = 1} * Nat.card {u : (ZMod B)ˣ // u ^ m = 1} := by
  let e : (ZMod (A * B))ˣ ≃* (ZMod A)ˣ × (ZMod B)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits
  rw [← Nat.card_prod]
  apply Nat.card_congr
  refine (e.toEquiv.subtypeEquiv (p := fun u => u ^ m = 1)
    (q := fun v => v.1 ^ m = 1 ∧ v.2 ^ m = 1) ?_).trans
    (Equiv.subtypeProdEquivProd (p := fun x : (ZMod A)ˣ => x ^ m = 1)
      (q := fun y : (ZMod B)ˣ => y ^ m = 1))
  intro u
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
  rw [← Prod.pow_fst, ← Prod.pow_snd, ← map_pow]
  constructor
  · intro hu; rw [hu, map_one]; simp
  · intro hu
    apply e.injective
    rw [map_one]
    exact Prod.ext hu.1 hu.2

theorem A072989_two_mod_four (A B : ℕ) (hA : 2 < A) (hB : 2 < B) (h : A.Coprime B)
    (h4 : (A * B) % 4 = 2) : A072989S (A * B) := by
  have hm0 : 0 < A * B := by positivity
  have hev : Even (A * B) := by rw [Nat.even_iff]; omega
  refine ⟨hm0, ?_⟩
  have hN : 4 ∣ A072989N (A * B) := by
    rw [A072989_N_eq_card (A * B) hm0, A072989_card_roots_eq_units (A * B) hm0.ne', A072989_card_split A B (A * B) h]
    have h1 := A072989_two_dvd_card A (A * B) hA hev
    have h2 := A072989_two_dvd_card B (A * B) hB hev
    have := Nat.mul_dvd_mul h1 h2
    simpa using this
  intro heq
  have h4m : 4 ∣ A * B := by
    rw [heq] at hN; exact hN.trans (Nat.gcd_dvd_left _ _)
  omega

theorem A072989_infinite : (Set.ofPred A072989S).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨b, hb⟩
  have hmem : A072989S (6 * 5 ^ (b + 1)) := by
    apply A072989_two_mod_four 6 (5 ^ (b + 1)) (by norm_num)
    · calc 2 < 5 := by norm_num
        _ ≤ 5 ^ (b + 1) := Nat.le_self_pow (by omega) 5
    · exact Nat.Coprime.pow_right _ (by norm_num)
    · rw [Nat.mul_mod, Nat.pow_mod]; norm_num
  have h1 := hb hmem
  have h2 : b < 5 ^ (b + 1) := by
    calc b < 5 ^ b := Nat.lt_pow_self (by norm_num)
      _ ≤ 5 ^ (b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem A072989_ge (n : ℕ) (hn : 1 ≤ n) : n ≤ A072989a n := by
  have hmono := Nat.nth_strictMono A072989_infinite
  have key : ∀ k, k + 1 ≤ Nat.nth A072989S k := by
    intro k
    induction k with
    | zero => exact (Nat.nth_mem_of_infinite A072989_infinite 0).1
    | succ k ih => have := hmono (Nat.lt_add_one k); omega
  have := key (n - 1)
  unfold A072989a; omega

/-- The conjecture "lim a(n)/n = 0" is false: a(n)/n ≥ 1 for all n ≥ 1. -/
theorem A072989_main :
    ¬ Tendsto (fun n : ℕ => (A072989a n : ℝ) / n) atTop (𝓝 0) := by
  intro h
  have hev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (A072989a n : ℝ) / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hpos, one_mul]
    exact_mod_cast A072989_ge n hn
  have := ge_of_tendsto h hev
  norm_num at this

