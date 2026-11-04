import Mathlib

/-
OEIS-A005408 (Mathlib). Conjecture (G. W. Adamson, 2012) on primes with one coach (A216371):
b = 4q ± 1 (q > 0) is in A216371 iff the top row of its coach is a permutation of the first q
odd numbers. README reading: the coach of an odd b (Hilton–Pedersen) has top row
a₀ = 1, a_{i+1} = odd part of (b − aᵢ), until it returns to 1; its coaches are the cycles of the
map a ↦ oddPart(b − a) on D(b) = {a odd, 2a < b, gcd(a, b) = 1}. README result: true.

Formalisation. `step b a = oddPart (b - a)` (oddPart n = n / 2^(v₂ n)), `D b` as above,
`coach1 b = {stepⁱ(1) : i ∈ ℕ}` (the entries of the top row of the coach of 1).
`step_bijOn`: for odd b, `step b` is a bijection of D(b) (maps D(b) to itself, injective), so
the coaches are its cycles and the top row of the coach of 1 lists `coach1 b` without
repetition. "b has one coach" is read as D(b) ⊆ coach1 b (the coach of 1 meets every
cycle, i.e. there is only one cycle), and "the top row is a permutation of the first q odd
numbers" as coach1 b = {a odd, a < 2q}.

Main theorem `A005408_main`: for odd b = 4q ± 1 with q > 0:
(b prime ∧ D(b) ⊆ coach1 b) ↔ coach1 b = {a | Odd a ∧ a < 2q}.

Outside Lean: nothing beyond the reading above (top row taken as the set of its entries;
`step_bijOn` shows the entries are distinct and the coaches are the cycles).
-/

def oddPart (n : ℕ) : ℕ := n / 2 ^ n.factorization 2

theorem oddPart_spec (n : ℕ) : 2 ^ n.factorization 2 * oddPart n = n :=
  Nat.ordProj_mul_ordCompl_eq_self n 2

theorem oddPart_odd {n : ℕ} (hn : n ≠ 0) : Odd (oddPart n) := by
  have := Nat.not_dvd_ordCompl Nat.prime_two hn
  rw [Nat.odd_iff]; unfold oddPart; omega

theorem oddPart_dvd (n : ℕ) : oddPart n ∣ n := Nat.ordCompl_dvd n 2

theorem two_oddPart_le {n : ℕ} (hn : n ≠ 0) (he : Even n) : 2 * oddPart n ≤ n := by
  have hs := oddPart_spec n
  rcases Nat.eq_zero_or_pos (n.factorization 2) with h0 | h0
  · rw [h0, pow_zero, one_mul] at hs
    have := oddPart_odd hn
    rw [hs] at this
    exact absurd he (Nat.not_even_iff_odd.mpr this)
  · have : 2 ≤ 2 ^ n.factorization 2 := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ n.factorization 2 := Nat.pow_le_pow_right (by norm_num) h0
    calc 2 * oddPart n ≤ 2 ^ n.factorization 2 * oddPart n := Nat.mul_le_mul_right _ this
      _ = n := hs

def step (b a : ℕ) : ℕ := oddPart (b - a)

def D (b : ℕ) : Set ℕ := {a | Odd a ∧ 2 * a < b ∧ Nat.Coprime a b}

def coach1 (b : ℕ) : Set ℕ := {a | ∃ i, (step b)^[i] 1 = a}

theorem step_mapsTo {b : ℕ} (hb : Odd b) : Set.MapsTo (step b) (D b) (D b) := by
  rintro a ⟨ha, h2a, hcop⟩
  have hc0 : b - a ≠ 0 := by omega
  have hce : Even (b - a) := by
    obtain ⟨i, hi⟩ := ha; obtain ⟨j, hj⟩ := hb; exact ⟨j - i, by omega⟩
  refine ⟨oddPart_odd hc0, ?_, ?_⟩
  · have := two_oddPart_le hc0 hce
    unfold step
    have : 1 ≤ a := by obtain ⟨i, hi⟩ := ha; omega
    omega
  · have h1 : Nat.Coprime (b - a) b := (Nat.coprime_self_sub_left (by omega)).mpr hcop
    exact Nat.Coprime.coprime_dvd_left (oddPart_dvd _) h1

theorem step_injOn {b : ℕ} : Set.InjOn (step b) (D b) := by
  rintro a ⟨_, h2a, _⟩ a' ⟨_, h2a', _⟩ he
  unfold step at he
  have hs := oddPart_spec (b - a)
  have hs' := oddPart_spec (b - a')
  set o := oddPart (b - a)
  set k := (b - a).factorization 2
  set k' := (b - a').factorization 2
  rw [he] at hs
  have ho : 0 < oddPart (b - a') := by
    rcases Nat.eq_zero_or_pos (oddPart (b - a')) with h | h
    · rw [h, mul_zero] at hs'; omega
    · exact h
  have key : ∀ m m' : ℕ, m < m' → 2 ^ m' * oddPart (b - a') ≥ 2 * (2 ^ m * oddPart (b - a')) := by
    intro m m' hm
    have : 2 ^ (m + 1) ≤ 2 ^ m' := Nat.pow_le_pow_right (by norm_num) hm
    rw [pow_succ] at this
    nlinarith
  rcases lt_trichotomy k k' with h | h | h
  · have := key k k' h; omega
  · rw [h] at hs; omega
  · have := key k' k h; omega

theorem D_finite (b : ℕ) : (D b).Finite :=
  (Set.finite_lt_nat b).subset (fun a ⟨_, h, _⟩ => by simp only [Set.mem_ofPred_eq]; omega)

/-- The coach map permutes D(b): the coaches are its cycles. -/
theorem step_bijOn {b : ℕ} (hb : Odd b) : Set.BijOn (step b) (D b) (D b) :=
  (Set.Finite.injOn_iff_bijOn_of_mapsTo (D_finite b) (step_mapsTo hb)).mp step_injOn

theorem coach1_sub_D {b : ℕ} (hb : Odd b) (h3 : 3 ≤ b) : coach1 b ⊆ D b := by
  rintro a ⟨i, rfl⟩
  induction i with
  | zero => exact ⟨odd_one, by simp; omega, Nat.coprime_one_left b⟩
  | succ i ih => rw [Function.iterate_succ_apply']; exact step_mapsTo hb ih

theorem A005408_main (b q : ℕ) (hb : Odd b) (hq : 0 < q) (hbq : b = 4 * q + 1 ∨ b + 1 = 4 * q) :
    (b.Prime ∧ D b ⊆ coach1 b) ↔ coach1 b = {a | Odd a ∧ a < 2 * q} := by
  have h3 : 3 ≤ b := by omega
  have hS : {a | Odd a ∧ a < 2 * q} = {a : ℕ | Odd a ∧ 2 * a < b} := by
    ext a; simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨j, rfl⟩, h⟩; exact ⟨⟨j, rfl⟩, by omega⟩
    · rintro ⟨⟨j, rfl⟩, h⟩; exact ⟨⟨j, rfl⟩, by omega⟩
  rw [hS]
  constructor
  · rintro ⟨hp, hsub⟩
    apply Set.Subset.antisymm
    · intro a ha; exact ⟨(coach1_sub_D hb h3 ha).1, (coach1_sub_D hb h3 ha).2.1⟩
    · rintro a ⟨ha, h2a⟩
      apply hsub
      refine ⟨ha, h2a, ?_⟩
      have ha0 : 0 < a := by obtain ⟨j, hj⟩ := ha; omega
      exact (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
        (Nat.not_dvd_of_pos_of_lt ha0 (by omega)))
  · intro heq
    have hall : ∀ a, Odd a → 2 * a < b → Nat.Coprime a b := by
      intro a ha h2a
      have : a ∈ coach1 b := by rw [heq]; exact ⟨ha, h2a⟩
      exact (coach1_sub_D hb h3 this).2.2
    refine ⟨?_, fun a ha => by rw [heq]; exact ⟨ha.1, ha.2.1⟩⟩
    by_contra hnp
    set p := b.minFac
    have hpp : p.Prime := Nat.minFac_prime (by omega)
    have hpd : p ∣ b := Nat.minFac_dvd b
    have hpb : p ≠ b := fun h => hnp (h ▸ hpp)
    obtain ⟨m, hm⟩ := hpd
    have hp2 : p ≠ 2 := by
      intro h; rw [h] at hm; obtain ⟨j, hj⟩ := hb; omega
    have hp3 : 3 ≤ p := by have := hpp.two_le; omega
    have hpm : p ≤ m := by
      have h1 : p ≤ b / p := Nat.minFac_le_div (by omega) hnp
      have hdiv : b / p = m := by rw [hm, Nat.mul_div_cancel_left _ (by omega : 0 < p)]
      rw [hdiv] at h1
      exact h1
    have hodd : Odd p := hpp.odd_of_ne_two hp2
    have h2p : 2 * p < b := by rw [hm]; nlinarith
    have := hall p hodd h2p
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_eq_left ⟨m, hm⟩] at this
    omega
