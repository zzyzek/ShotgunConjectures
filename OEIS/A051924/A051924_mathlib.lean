import Mathlib

/-
OEIS-A051924 (Mathlib). a(n) = C(2n, n) - C(2n-2, n-1). Conjecture (G. Detlefs, 2013):
a(n) mod n² = n + 2 iff n is an odd prime. README result: false, n = 16843² = 283686649 is
composite and a(n) ≡ n + 2 (mod n²); the "if" direction holds.

Main theorem `A051924_main`:
* every odd prime p has a(p) % p² = p + 2 (the "if" direction, for all odd primes, by the
  Babbage-type congruence C(2p-1, p-1) ≡ 1 (mod p²));
* n = 283686649 = 16843² is odd, not prime, and a(n) % n² = n + 2.
`A051924_false`: the conjecture `∀ n, a(n) % n² = n + 2 ↔ (n prime ∧ n odd)` is false.

Proof. `a_mul`: a(n)·(2n-1) = C(2n-1, n-1)·(3n-2); since (n+2)(2n-1) = (3n-2) + 2n² and
gcd(2n-1, n) = 1, a(n) ≡ n + 2 (mod n²) follows from C(2n-1, n-1) ≡ 1 (mod n²) (`a_of_choose`).
`choose_mul_fact`: C(2n-1, n-1)·∏_{k<n} k = ∏_{1≤k<n} (n+k). `pair_prod`: for odd n, pairing
k with n - k, (n+k)(2n-k) = k(n-k) + 2n², so ∏ over any k ↦ n-k symmetric set of (n+k) is
≡ ∏ k (mod n²). For n = p this gives C(2p-1, p-1) ≡ 1 (mod p²). For n = p², split
k into p ∤ k (paired, ≡ mod p⁴) and k = pj (giving p^(p-1)·∏(p+j) and p^(p-1)·∏ j); with the
kernel computation ∏_{j<p}(p+j) ≡ ∏_{j<p} j (mod p⁴) for p = 16843 (binary-splitting product
`prodMod`, proved correct), C(2n-1, n-1) ≡ 1 (mod p⁴ = n²).

Outside Lean: nothing.
-/

open Finset

/-- OEIS A051924. -/
def a (n : ℕ) : ℕ := (2 * n).choose n - (2 * n - 2).choose (n - 1)

theorem a_mul (m : ℕ) : a (m + 1) * (2 * m + 1) = (2 * m + 1).choose m * (3 * m + 1) := by
  have e0 : a (m + 1) = (2 * m + 1 + 1).choose (m + 1) - (2 * m).choose m := by
    unfold a; congr 2
  have e1 : (2 * m + 1 + 1).choose (m + 1) = 2 * (2 * m + 1).choose m := by
    rw [Nat.choose_succ_succ', Nat.choose_symm_half]; ring
  have e2 := Nat.add_one_mul_choose_eq (2 * m) m
  rw [show 2 * m + 1 = 2 * m + 1 from rfl, Nat.choose_symm_half] at e2
  rw [e0, e1]
  set c := (2 * m + 1).choose m
  set e := (2 * m).choose m
  have hle : e ≤ 2 * c := by nlinarith
  zify [hle]
  zify at e2
  linear_combination (-1 : ℤ) * e2

theorem cop_odd (m : ℕ) : Nat.Coprime ((m + 1) ^ 2) (2 * m + 1) := by
  apply Nat.Coprime.pow_left
  rw [show 2 * m + 1 = m + (m + 1) by ring, Nat.coprime_add_self_right,
    show m + 1 = 1 + m by ring, Nat.coprime_add_self_left]
  exact Nat.coprime_one_left m

theorem a_of_choose (m : ℕ) (hm : 2 ≤ m) (hC : (2 * m + 1).choose m ≡ 1 [MOD (m + 1) ^ 2]) :
    a (m + 1) % (m + 1) ^ 2 = m + 1 + 2 := by
  have h1 : a (m + 1) * (2 * m + 1) ≡ (m + 1 + 2) * (2 * m + 1) [MOD (m + 1) ^ 2] := by
    rw [a_mul]
    have h2 : (m + 1 + 2) * (2 * m + 1) = 1 * (3 * m + 1) + 2 * (m + 1) ^ 2 := by ring
    rw [h2]
    have h3 : 1 * (3 * m + 1) + 2 * (m + 1) ^ 2 ≡ 1 * (3 * m + 1) [MOD (m + 1) ^ 2] := by
      unfold Nat.ModEq; simp [Nat.add_mul_mod_self_right]
    exact (hC.mul_right _).trans h3.symm
  have h4 := Nat.ModEq.cancel_right_of_coprime (cop_odd m) h1
  unfold Nat.ModEq at h4
  rw [h4]
  apply Nat.mod_eq_of_lt
  nlinarith

/-- C(2n-1, n-1)·(n-1)! = ∏_{1 ≤ k < n} (n + k), with n = m + 1. -/
theorem choose_mul_fact (m : ℕ) :
    (2 * m + 1).choose m * ∏ k ∈ Ico 1 (m + 1), k = ∏ k ∈ Ico 1 (m + 1), (m + 1 + k) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (n := 2 * m + 1) (k := m) (by omega)
  rw [show 2 * m + 1 - m = m + 1 by omega] at h1
  have h2 : (2 * m + 1).factorial = (m + 1).factorial * ∏ k ∈ Ico 1 (m + 1), (m + 1 + k) := by
    rw [← prod_Ico_id_eq_factorial, ← prod_Ico_id_eq_factorial,
      ← prod_Ico_consecutive _ (show 1 ≤ m + 1 + 1 by omega) (show m + 1 + 1 ≤ 2 * m + 1 + 1 by omega)]
    congr 1
    rw [show m + 1 + 1 = 1 + (m + 1) by ring, show 2 * m + 1 + 1 = (m + 1) + (m + 1) by ring,
      ← prod_Ico_add']
    exact prod_congr rfl (fun k _ => by ring)
  rw [prod_Ico_id_eq_factorial]
  have hf : 0 < (m + 1).factorial := Nat.factorial_pos _
  rw [h2] at h1
  have : (m + 1).factorial * ((2 * m + 1).choose m * m.factorial) =
      (m + 1).factorial * ∏ k ∈ Ico 1 (m + 1), (m + 1 + k) := by rw [← h1]; ring
  exact Nat.eq_of_mul_eq_mul_left hf this

/-- Pairing k with 2m+1-k in a product. -/
theorem pair_prod {R : Type*} [CommMonoid R] (f g : ℕ → R) (m : ℕ)
    (h : ∀ k, 1 ≤ k → k ≤ m → f k * f (2 * m + 1 - k) = g k * g (2 * m + 1 - k)) :
    ∏ k ∈ Ico 1 (2 * m + 1), f k = ∏ k ∈ Ico 1 (2 * m + 1), g k := by
  have split : ∀ F : ℕ → R, ∏ k ∈ Ico 1 (2 * m + 1), F k =
      ∏ k ∈ Ico 1 (m + 1), (F k * F (2 * m + 1 - k)) := by
    intro F
    rw [← prod_Ico_consecutive _ (show 1 ≤ m + 1 by omega) (show m + 1 ≤ 2 * m + 1 by omega),
      prod_mul_distrib]
    congr 1
    rw [prod_Ico_reflect F 1 (show m + 1 ≤ 2 * m + 1 + 1 by omega),
      show 2 * m + 1 + 1 - (m + 1) = m + 1 by omega, show 2 * m + 1 + 1 - 1 = 2 * m + 1 by omega]
  rw [split f, split g]
  exact prod_congr rfl (fun k hk => by
    rw [mem_Ico] at hk; exact h k hk.1 (by omega))

/-- For odd n = 2m+1 and a predicate P symmetric under k ↦ n - k: modulo n²,
∏_{1≤k<n, P k} (n + k) ≡ ∏_{1≤k<n, P k} k. -/
theorem pair_mod (m : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ k, 1 ≤ k → k ≤ m → (P (2 * m + 1 - k) ↔ P k)) :
    ((∏ k ∈ Ico 1 (2 * m + 1), (if P k then 2 * m + 1 + k else 1) : ℕ) : ZMod ((2 * m + 1) ^ 2)) =
      ((∏ k ∈ Ico 1 (2 * m + 1), (if P k then k else 1) : ℕ) : ZMod ((2 * m + 1) ^ 2)) := by
  rw [Nat.cast_prod, Nat.cast_prod]
  apply pair_prod
  intro k hk1 hkm
  have hk' := hP k hk1 hkm
  by_cases hk : P k
  · have hk2 : P (2 * m + 1 - k) := hk'.mpr hk
    simp only [hk, hk2, ite_true]
    set j := 2 * m + 1 - k
    have hj : k + j = 2 * m + 1 := by omega
    have e : (2 * m + 1 + k) * (2 * m + 1 + j) = k * j + 2 * (2 * m + 1) ^ 2 := by
      rw [← hj]; ring
    rw [← Nat.cast_mul, ← Nat.cast_mul, e, Nat.cast_add, Nat.cast_mul (2 : ℕ),
      ZMod.natCast_self, mul_zero, add_zero]
  · have hk2 : ¬ P (2 * m + 1 - k) := fun h => hk (hk'.mp h)
    simp only [hk, hk2, ite_false]

theorem mod_of_zmod {a b N : ℕ} (h : (a : ZMod N) = (b : ZMod N)) : a ≡ b [MOD N] :=
  (ZMod.natCast_eq_natCast_iff a b N).mp h

/-- Babbage: C(2p-1, p-1) ≡ 1 (mod p²) for an odd prime p = 2m+1. -/
theorem babbage (m : ℕ) (hp : (2 * m + 1).Prime) :
    (2 * (2 * m) + 1).choose (2 * m) ≡ 1 [MOD (2 * m + 1) ^ 2] := by
  have key := pair_mod m (fun _ => True) (fun _ _ _ => Iff.rfl)
  simp only [ite_true] at key
  have hmod := mod_of_zmod key
  rw [← choose_mul_fact (2 * m)] at hmod
  have hcop : Nat.Coprime ((2 * m + 1) ^ 2) (∏ k ∈ Ico 1 (2 * m + 1), k) := by
    apply Nat.Coprime.pow_left
    apply Nat.Coprime.prod_right
    intro k hk
    rw [mem_Ico] at hk
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt (by omega) hk.2)
  exact Nat.ModEq.cancel_right_of_coprime hcop (by rw [one_mul]; exact hmod)

/-- Product a·(a+1)···(a+len-1) mod M by binary splitting (fuel bounds the depth). -/
def prodMod (M : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, a, len => (∏ i ∈ range len, (a + i)) % M
  | f + 1, a, len =>
    if len = 0 then 1 % M
    else if len = 1 then a % M
    else prodMod M f a (len / 2) * prodMod M f (a + len / 2) (len - len / 2) % M

theorem prodMod_eq (M : ℕ) : ∀ f a len, prodMod M f a len = (∏ i ∈ range len, (a + i)) % M
  | 0, a, len => rfl
  | f + 1, a, len => by
    unfold prodMod
    split_ifs with h0 h1
    · subst h0; simp
    · subst h1; simp
    · rw [prodMod_eq M f, prodMod_eq M f, ← Nat.mul_mod]
      congr 1
      conv_rhs => rw [show len = len / 2 + (len - len / 2) by omega]
      rw [prod_range_add]
      exact congrArg _ (prod_congr rfl (fun i _ => by ring))

theorem wolst_16843 :
    (∏ k ∈ Ico 1 16843, (16843 + k)) ≡ ∏ k ∈ Ico 1 16843, k [MOD 16843 ^ 4] := by
  rw [prod_Ico_eq_prod_range, prod_Ico_eq_prod_range]
  have e1 : ∏ k ∈ range (16843 - 1), (16843 + (1 + k)) = ∏ k ∈ range 16842, (16844 + k) :=
    prod_congr rfl (fun k _ => by ring)
  have e2 : ∏ k ∈ range (16843 - 1), (1 + k) = ∏ k ∈ range 16842, (1 + k) := rfl
  rw [e1, e2]
  unfold Nat.ModEq
  rw [← prodMod_eq _ 20, ← prodMod_eq _ 20]
  decide +kernel

theorem split_prod (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (F : ℕ → ℕ) :
    ∏ k ∈ s, F k = (∏ k ∈ s, (if ¬ P k then F k else 1)) * ∏ k ∈ s, (if P k then F k else 1) := by
  rw [← prod_mul_distrib]
  exact prod_congr rfl (fun k _ => by by_cases h : P k <;> simp [h])

theorem div_part (p : ℕ) (hp : 2 ≤ p) (F : ℕ → ℕ) :
    ∏ k ∈ Ico 1 (p ^ 2), (if p ∣ k then F k else 1) = ∏ j ∈ Ico 1 p, F (p * j) := by
  rw [← prod_filter]
  have e : (Ico 1 (p ^ 2)).filter (fun k => p ∣ k) = (Ico 1 p).image (fun j => p * j) := by
    ext k
    simp only [mem_filter, mem_Ico, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨j, rfl⟩⟩
      refine ⟨j, ⟨?_, ?_⟩, rfl⟩
      · rcases j with _ | j
        · simp at h1
        · omega
      · rw [sq] at h2; exact Nat.lt_of_mul_lt_mul_left h2
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨j, rfl⟩⟩
      · nlinarith
      · rw [sq]; exact Nat.mul_lt_mul_of_pos_left h2 (by omega)
  rw [e, prod_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left (by omega) h)]

/-- For n = p² (p an odd prime) with ∏_{1≤j<p}(p+j) ≡ ∏_{1≤j<p} j (mod p⁴):
C(2n-1, n-1) ≡ 1 (mod n²). -/
theorem sq_case (p M : ℕ) (hp : p.Prime) (hM : p ^ 2 = 2 * M + 1)
    (hw : ∏ k ∈ Ico 1 p, (p + k) ≡ ∏ k ∈ Ico 1 p, k [MOD p ^ 4]) :
    (2 * (2 * M) + 1).choose (2 * M) ≡ 1 [MOD (2 * M + 1) ^ 2] := by
  have hp2 := hp.two_le
  have hn4 : (2 * M + 1) ^ 2 = p ^ 4 := by rw [← hM]; ring
  rw [hn4]
  have hcf := choose_mul_fact (2 * M)
  rw [← hM, split_prod _ (fun k => p ∣ k) (fun k => k),
    split_prod _ (fun k => p ∣ k) (fun k => p ^ 2 + k), div_part p hp2, div_part p hp2] at hcf
  have hD : ∏ j ∈ Ico 1 p, (p ^ 2 + p * j) = p ^ (p - 1) * ∏ j ∈ Ico 1 p, (p + j) := by
    rw [show p ^ (p - 1) = ∏ _j ∈ Ico 1 p, p by rw [prod_const, Nat.card_Ico], ← prod_mul_distrib]
    exact prod_congr rfl (fun j _ => by ring)
  have hE : ∏ j ∈ Ico 1 p, (p * j) = p ^ (p - 1) * ∏ j ∈ Ico 1 p, j := by
    rw [show p ^ (p - 1) = ∏ _j ∈ Ico 1 p, p by rw [prod_const, Nat.card_Ico], ← prod_mul_distrib]
  rw [hD, hE] at hcf
  set C := (2 * (2 * M) + 1).choose (2 * M)
  set G := ∏ k ∈ Ico 1 (p ^ 2), (if ¬ p ∣ k then p ^ 2 + k else 1)
  set H := ∏ k ∈ Ico 1 (p ^ 2), (if ¬ p ∣ k then k else 1)
  set Pp := ∏ j ∈ Ico 1 p, (p + j)
  set Fp := ∏ j ∈ Ico 1 p, j
  have hc : 0 < p ^ (p - 1) := pow_pos (by omega) _
  have h1 : C * (H * Fp) = G * Pp := by
    apply Nat.eq_of_mul_eq_mul_left hc
    calc p ^ (p - 1) * (C * (H * Fp)) = C * (H * (p ^ (p - 1) * Fp)) := by ring
      _ = G * (p ^ (p - 1) * Pp) := hcf
      _ = p ^ (p - 1) * (G * Pp) := by ring
  have hsym : ∀ k, 1 ≤ k → k ≤ M → ((¬ p ∣ (2 * M + 1 - k)) ↔ ¬ p ∣ k) := by
    intro k _ hkM
    have hpn : p ∣ 2 * M + 1 := ⟨p, by rw [← hM]; ring⟩
    constructor
    · intro h hk; exact h (Nat.dvd_sub hpn hk)
    · intro h hk
      apply h
      have : k = 2 * M + 1 - (2 * M + 1 - k) := by omega
      rw [this]; exact Nat.dvd_sub hpn hk
  have hGH := mod_of_zmod (pair_mod M (fun k => ¬ p ∣ k) hsym)
  rw [← hM, show (p ^ 2) ^ 2 = p ^ 4 by ring] at hGH
  have hGH' : G ≡ H [MOD p ^ 4] := hGH
  have h2 : C * (H * Fp) ≡ 1 * (H * Fp) [MOD p ^ 4] := by
    rw [h1, one_mul]
    calc G * Pp ≡ H * Pp [MOD p ^ 4] := hGH'.mul_right _
      _ ≡ H * Fp [MOD p ^ 4] := hw.mul_left _
  have hcop : Nat.Coprime (p ^ 4) (H * Fp) := by
    apply Nat.Coprime.pow_left
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.prod_right
      intro k _
      by_cases hk : p ∣ k
      · simp [hk]
      · simp only [hk, not_false_eq_true, ite_true]
        exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hk
    · apply Nat.Coprime.prod_right
      intro k hk
      rw [mem_Ico] at hk
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt (by omega) hk.2)
  exact Nat.ModEq.cancel_right_of_coprime hcop h2

theorem p_prime : Nat.Prime 16843 := by norm_num

theorem A051924_main :
    (∀ p : ℕ, p.Prime → Odd p → a p % p ^ 2 = p + 2) ∧
      (283686649 = 16843 ^ 2 ∧ Odd 283686649 ∧ ¬ Nat.Prime 283686649 ∧
        a 283686649 % 283686649 ^ 2 = 283686649 + 2) := by
  refine ⟨?_, by norm_num, by decide, ?_, ?_⟩
  · intro p hp ho
    obtain ⟨m, rfl⟩ := ho
    have h3 : 1 ≤ m := by
      rcases m with _ | m
      · exact absurd hp (by norm_num)
      · omega
    have := a_of_choose (2 * m) (by omega) (babbage m hp)
    simpa using this
  · rw [show (283686649 : ℕ) = 16843 * 16843 by norm_num]
    exact Nat.not_prime_mul (by norm_num) (by norm_num)
  · have h := sq_case 16843 141843324 p_prime (by norm_num) wolst_16843
    have := a_of_choose (2 * 141843324) (by norm_num) h
    norm_num at this ⊢
    exact this

theorem A051924_false : ¬ ∀ n : ℕ, (a n % n ^ 2 = n + 2 ↔ n.Prime ∧ Odd n) := by
  intro h
  obtain ⟨-, -, -, hc, ha⟩ := A051924_main
  exact hc ((h 283686649).mp ha).1
