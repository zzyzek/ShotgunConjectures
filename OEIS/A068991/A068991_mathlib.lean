/-
OEIS A068991: numbers k such that Sum_{d | k} sigma(d)/phi(d) is an integer.
Conjecture (Benoit Cloitre): if k is in the sequence and k is squarefree, then k divides the
denominator of the Bernoulli number B_{2k}.

Checked here (Mathlib): `A068991_conjecture`: for squarefree k with
Sum_{d | k} sigma(d)/phi(d) an integer (computed in ℚ), k ∣ (bernoulli (2 * k)).den.
The proof uses Mathlib's von Staudt-Clausen consequence `Bernoulli.dvd_den_bernoulli`.
Nothing is outside Lean.
-/
import Mathlib

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Products over a finite set of primes. -/
def Kp (s : Finset ℕ) : ℕ := ∏ p ∈ s, p
def Dp (s : Finset ℕ) : ℕ := ∏ p ∈ s, (p - 1)

/-- The invariant carried along the induction (F = 2^|s| K / D). -/
def A068991Inv (s : Finset ℕ) (F : ℕ) : Prop :=
  (∀ p ∈ s, (p - 1) ∣ 2 * Kp s) ∧ (¬ 2 ∣ Kp s → ¬ 2 ∣ F) ∧
  (4 ∣ F → (Kp s = 2 ∧ F = 4) ∨ (Kp s = 6 ∧ F = 12) ∨ (Kp s = 42 ∧ F = 28))

lemma A068991_not_dvd_Dp {s : Finset ℕ} {M : ℕ} (hM : M.Prime) (hs : ∀ p ∈ s, p.Prime)
    (hlt : ∀ x ∈ s, x < M) : ¬ M ∣ Dp s := by
  intro h
  obtain ⟨p, hp, hdvd⟩ := (Prime.dvd_finsetProd_iff hM.prime _).1 h
  have h1 := (hs p hp).two_le
  have := Nat.le_of_dvd (by omega) hdvd
  have := hlt p hp
  omega

lemma A068991_not_dvd_Kp {s : Finset ℕ} {M : ℕ} (hM : M.Prime) (hs : ∀ p ∈ s, p.Prime)
    (hlt : ∀ x ∈ s, x < M) : ¬ M ∣ Kp s := by
  intro h
  obtain ⟨p, hp, hdvd⟩ := (Prime.dvd_finsetProd_iff hM.prime _).1 h
  have := (Nat.prime_dvd_prime_iff_eq hM (hs p hp)).1 hdvd
  have := hlt p hp
  omega

/-- h ∣ K from h ∣ F, F ∣ 2^n K, in the two cases K odd / F odd and K even / 4 ∤ F. -/
lemma A068991_dvd_K {h F K n : ℕ} (hh : h ∣ F) (hF : F ∣ 2 ^ n * K) (_hK : K ≠ 0)
    (hc : (¬ 2 ∣ K ∧ ¬ 2 ∣ F) ∨ (2 ∣ K ∧ ¬ 4 ∣ F)) : h ∣ K := by
  have hF0 : F ≠ 0 := by rintro rfl; simp at hF; omega
  have hh0 : h ≠ 0 := by rintro rfl; simp at hh; exact hF0 hh
  obtain ⟨a, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hh0
  have hu2 : u.Coprime (2 ^ n) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hu)
  have huK : u ∣ K := hu2.dvd_of_dvd_mul_left
    ((Dvd.intro_left _ rfl).trans (hh.trans hF))
  have h2a : 2 ^ a ∣ F := (Dvd.intro _ rfl).trans hh
  have hcop : (2 ^ a).Coprime u := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hu)
  apply hcop.mul_dvd_of_dvd_of_dvd _ huK
  rcases hc with ⟨-, hF2⟩ | ⟨hK2, hF4⟩
  · rcases a with _ | a
    · simp
    · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero a)).trans h2a) hF2
  · rcases a with _ | _ | a
    · simp
    · simpa using hK2
    · exact absurd ((Dvd.intro_left (2 ^ a) (by ring)).trans h2a) hF4

theorem A068991_core (s : Finset ℕ) :
    (∀ p ∈ s, p.Prime) → ∀ F, F * Dp s = 2 ^ s.card * Kp s → A068991Inv s F := by
  induction s using Finset.induction_on_max with
  | empty =>
    intro _ F hF
    simp [Dp, Kp] at hF
    subst hF
    refine ⟨by simp, by simp, by omega⟩
  | insert M s hlt ih =>
    intro hs F hF
    have hMs : M ∉ s := fun h => lt_irrefl _ (hlt M h)
    have hM : M.Prime := hs M (mem_insert_self _ _)
    have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (mem_insert_of_mem hp)
    have hK : Kp (insert M s) = M * Kp s := by simp [Kp, prod_insert hMs]
    have hD : Dp (insert M s) = (M - 1) * Dp s := by simp [Dp, prod_insert hMs]
    have hcard : (insert M s).card = s.card + 1 := card_insert_of_notMem hMs
    unfold A068991Inv
    rw [hK, hD, hcard] at hF
    rw [hK]
    have hKpos : Kp s ≠ 0 := by
      simp only [Kp]; exact prod_ne_zero_iff.2 fun p hp => (hs' p hp).ne_zero
    have hnD := A068991_not_dvd_Dp hM hs' hlt
    have hnK := A068991_not_dvd_Kp hM hs' hlt
    rcases hM.eq_two_or_odd' with rfl | hodd
    · -- M = 2: s is empty
      have hse : s = ∅ := by
        apply eq_empty_of_forall_notMem
        intro x hx
        have := (hs' x hx).two_le
        have := hlt x hx
        omega
      subst hse
      simp [Kp, Dp] at hF ⊢
      subst hF
      decide
    · obtain ⟨h, rfl⟩ := hodd
      have hsub : 2 * h + 1 - 1 = 2 * h := by omega
      rw [hsub] at hF
      have hh0 : 0 < h := by have := hM.two_le; omega
      -- M ∣ F
      have hMF : (2 * h + 1) ∣ F := by
        have h1 : (2 * h + 1) ∣ F * h * Dp s := by
          refine ⟨2 ^ s.card * Kp s, ?_⟩
          have : 2 * (F * h * Dp s) = 2 * ((2 * h + 1) * (2 ^ s.card * Kp s)) := by
            calc 2 * (F * h * Dp s) = F * (2 * h * Dp s) := by ring
              _ = 2 ^ (s.card + 1) * ((2 * h + 1) * Kp s) := hF
              _ = _ := by ring
          omega
        rcases (Nat.Prime.dvd_mul hM).1 h1 with h2 | h2
        · rcases (Nat.Prime.dvd_mul hM).1 h2 with h3 | h3
          · exact h3
          · exact absurd (Nat.le_of_dvd hh0 h3) (by omega)
        · exact absurd h2 hnD
      obtain ⟨G, rfl⟩ := hMF
      have hG : (G * h) * Dp s = 2 ^ s.card * Kp s := by
        have hpos : 0 < 2 * h + 1 := by omega
        have : (2 * h + 1) * (2 * ((G * h) * Dp s)) =
            (2 * h + 1) * (2 * (2 ^ s.card * Kp s)) := by
          calc (2 * h + 1) * (2 * ((G * h) * Dp s)) = (2 * h + 1) * G * (2 * h * Dp s) := by ring
            _ = 2 ^ (s.card + 1) * ((2 * h + 1) * Kp s) := hF
            _ = _ := by ring
        have := Nat.eq_of_mul_eq_mul_left hpos this
        omega
      obtain ⟨iha, ihb, ihc⟩ := ih hs' (G * h) hG
      have hFdvd : G * h ∣ 2 ^ s.card * Kp s := Dvd.intro _ hG
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        rcases mem_insert.1 hp with rfl | hp
        · -- p = M
          rw [hsub, show 2 * ((2 * h + 1) * Kp s) = (2 * h + 1) * (2 * Kp s) by ring]
          apply dvd_mul_of_dvd_right
          apply mul_dvd_mul_left
          by_cases h4 : 4 ∣ G * h
          · rcases ihc h4 with ⟨hk, hf⟩ | ⟨hk, hf⟩ | ⟨hk, hf⟩ <;> rw [hk] <;>
            · have hle : h ≤ G * h := Nat.le_of_dvd (by omega) (Dvd.intro_left _ rfl)
              have hd : h ∣ G * h := Dvd.intro_left _ rfl
              rw [hf] at hd hle
              interval_cases h <;> first | decide | (exfalso; revert hM; decide) |
                (exfalso; revert hd; decide)
          · apply A068991_dvd_K (Dvd.intro_left _ rfl) hFdvd hKpos
            by_cases hk2 : 2 ∣ Kp s
            · exact Or.inr ⟨hk2, h4⟩
            · exact Or.inl ⟨hk2, ihb hk2⟩
        · exact (iha p hp).trans (by
            rw [show 2 * ((2 * h + 1) * Kp s) = (2 * h + 1) * (2 * Kp s) by ring]
            exact dvd_mul_left _ _)
      · intro hk2 hF2
        have hk2' : ¬ 2 ∣ Kp s := fun h' => hk2 (dvd_mul_of_dvd_right h' _)
        have := ihb hk2'
        apply this
        exact dvd_mul_of_dvd_left ((Nat.coprime_two_left.2 (odd_two_mul_add_one h)).dvd_of_dvd_mul_left hF2) _
      · intro h4
        have h4' : 4 ∣ G * h := by
          have : 4 ∣ (2 * h + 1) * (G * h) := by
            rcases h4 with ⟨c, hc⟩; exact ⟨c * h, by rw [show (2*h+1) * (G*h) = (2*h+1)*G*h by ring, hc]; ring⟩
          have hc4 : Nat.Coprime (2 ^ 2) (2 * h + 1) :=
            Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 (odd_two_mul_add_one h))
          exact hc4.dvd_of_dvd_mul_left this
        rcases ihc h4' with ⟨hk, hf⟩ | ⟨hk, hf⟩ | ⟨hk, hf⟩ <;> rw [hk] at hnK ⊢
        · have hd : h ∣ 4 := hf ▸ Dvd.intro_left _ rfl
          have hle := Nat.le_of_dvd (by norm_num) hd
          interval_cases h <;> omega
        · have hd : h ∣ 12 := hf ▸ Dvd.intro_left _ rfl
          have hle := Nat.le_of_dvd (by norm_num) hd
          interval_cases h <;> omega
        · have hd : h ∣ 28 := hf ▸ Dvd.intro_left _ rfl
          have hle := Nat.le_of_dvd (by norm_num) hd
          interval_cases h <;> first | omega | (norm_num at hM)

/-- σ(d)/φ(d) as a ℚ-valued arithmetic function. -/
noncomputable def A068991g : ArithmeticFunction ℚ :=
  ⟨fun d => (σ 1 d : ℚ) / (Nat.totient d : ℚ), by simp⟩

lemma A068991g_apply (d : ℕ) : A068991g d = (σ 1 d : ℚ) / (Nat.totient d : ℚ) := rfl

lemma A068991g_mult : A068991g.IsMultiplicative := by
  refine ⟨by simp [A068991g_apply], fun {m n} hmn => ?_⟩
  simp only [A068991g_apply, isMultiplicative_sigma.map_mul_of_coprime hmn, Nat.totient_mul hmn]
  push_cast
  rw [div_mul_div_comm]

lemma A068991g_prime {p : ℕ} (hp : p.Prime) :
    1 + A068991g p = 2 * (p : ℚ) / ((p - 1 : ℕ) : ℚ) := by
  have h1 : σ 1 p = p + 1 := by
    have := sigma_one_apply_prime_pow (i := 1) hp
    simp [Finset.sum_range_succ] at this
    rw [this]; ring
  have h2 : (1 : ℚ) ≤ p := by exact_mod_cast hp.one_lt.le
  have h3 : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by rw [Nat.cast_sub hp.one_lt.le]; simp
  have h4 : (p : ℚ) - 1 ≠ 0 := by
    have : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
    linarith
  rw [A068991g_apply, h1, Nat.totient_prime hp, h3]
  push_cast
  field_simp
  ring

/-- Closed form: for squarefree k, Sum_{d | k} σ(d)/φ(d) = 2^ω(k) k / Π_{p | k} (p - 1). -/
theorem A068991_closed_form {k : ℕ} (hk : Squarefree k) :
    (∑ d ∈ k.divisors, (σ 1 d : ℚ) / (Nat.totient d : ℚ)) =
      (2 ^ k.primeFactors.card * Kp k.primeFactors : ℕ) / (Dp k.primeFactors : ℚ) := by
  have := A068991g_mult.prodPrimeFactors_one_add_of_squarefree hk
  rw [show (∑ d ∈ k.divisors, (σ 1 d : ℚ) / (Nat.totient d : ℚ)) =
      ∑ d ∈ k.divisors, A068991g d from rfl, ← this]
  rw [Finset.prod_congr rfl fun p hp => A068991g_prime (Nat.prime_of_mem_primeFactors hp)]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const]
  simp [Kp, Dp]

/-- Main theorem (Cloitre's conjecture in A068991): if k is squarefree and
Sum_{d | k} σ(d)/φ(d) is an integer, then k divides the denominator of B_{2k}. -/
theorem A068991_conjecture (k : ℕ) (hk : Squarefree k)
    (hint : ∃ z : ℤ, (∑ d ∈ k.divisors, (σ 1 d : ℚ) / (Nat.totient d : ℚ)) = z) :
    k ∣ (bernoulli (2 * k)).den := by
  obtain ⟨z, hz⟩ := hint
  have hk0 : k ≠ 0 := hk.ne_zero
  rw [A068991_closed_form hk] at hz
  set s := k.primeFactors with hs_def
  have hsP : ∀ p ∈ s, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hKk : Kp s = k := Nat.prod_primeFactors_of_squarefree hk
  have hD0 : (Dp s : ℚ) ≠ 0 := by
    have : Dp s ≠ 0 := prod_ne_zero_iff.2 fun p hp => by
      have := (hsP p hp).two_le; omega
    exact_mod_cast this
  -- z * D = 2^n K as integers, so z ≥ 0
  have hzD : (z : ℚ) * (Dp s : ℚ) = ((2 ^ s.card * Kp s : ℕ) : ℚ) := by
    rw [← hz]; field_simp
  have hzD' : z * (Dp s : ℤ) = ((2 ^ s.card * Kp s : ℕ) : ℤ) := by exact_mod_cast hzD
  have hz0 : 0 ≤ z := by
    by_contra hneg
    replace hneg := lt_of_not_ge hneg
    have : z * (Dp s : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le (by positivity)
    have : (0 : ℤ) < ((2 ^ s.card * Kp s : ℕ) : ℤ) := by
      have : 0 < 2 ^ s.card * Kp s := Nat.mul_pos (by positivity) (by omega)
      exact_mod_cast this
    omega
  have hF : z.toNat * Dp s = 2 ^ s.card * Kp s := by
    have : ((z.toNat * Dp s : ℕ) : ℤ) = ((2 ^ s.card * Kp s : ℕ) : ℤ) := by
      push_cast; rw [Int.toNat_of_nonneg hz0]; exact hzD'
    exact_mod_cast this
  obtain ⟨ha, -, -⟩ := A068991_core s hsP z.toNat hF
  rw [hKk] at ha
  have hk0' : 0 < k := Nat.pos_of_ne_zero hk0
  conv_lhs => rw [← hKk]
  refine Finset.prod_primes_dvd _ (fun p hp => (hsP p hp).prime) fun p hp => ?_
  have := Fact.mk (hsP p hp)
  exact Bernoulli.dvd_den_bernoulli hk0' (ha p hp)
