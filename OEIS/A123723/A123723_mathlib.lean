/-
OEIS A123723, Mathlib proof of J. W. Layman's conjecture (2006).

A000224(n) = number of squares mod n = `A123723_S n` = #{x^2 mod n : 0 ≤ x < n}.
A123723 lists the n ≥ 1 with A000224(n) = ⌈(n+1)/4⌉; in ℕ, ⌈(n+1)/4⌉ = n/4 + 1
(`A123723_P`). a(n) = `Nat.nth A123723_P (n - 1)` (offset 1).

Main theorem `A123723_main`: for every n > 4, if 4 ∣ a(n) then a(n)/4 is prime.
`A123723_classify`: for N > 0 with 4 ∣ N, N ≠ 4 and S(N) = N/4 + 1, N/4 is prime.
`A123723_data`: the members below 64 are 1, 4, 8, 12, 20, 28, 44, 45, 52, 63 (OEIS data).
`A123723_four_mul_prime`: 4p is a member for every odd prime p (so the set is infinite).

Proof. The general lemmas are those of OEIS/A123722/A123722_mathlib.lean (copied with the
prefix A123723): S multiplicative (CRT), S(m) ≤ m/2 + 1, S(m) ≤ m/2 if d^2 ∣ m (d ≥ 2),
2S(p) = p + 1 for odd primes, hence 2S(m) = m + 1 with m odd forces m = 1 or m prime
(`A123723_L`), and S(N) ≤ S(M)·N/M for M ∣ N. Write N = 2^j r with r odd, j ≥ 2.
j = 2: S(N) = 2S(r) = r + 1, so r is prime (r = 1 is N = 4). j = 3: 3S(r) = 2r + 1 and
2S(r) ≤ r + 1 give r = 1, N = 8. j ≥ 4: S(2^j) ≤ 3·2^(j-3) (squares mod 8 are 0, 1, 4) rules
out r ≥ 3; for r = 1, S(16) = 4 ≠ 5 and S(2^j) ≤ 7·2^(j-5) < 2^(j-2) + 1 for j ≥ 5 (seven
squares mod 32).

Not checked in Lean: nothing for the statement above.
-/
import Mathlib

open Finset

/-- The number of squares mod n (A000224); `A123723_S 0 = 0`. -/
def A123723_S (n : ℕ) : ℕ := ((range n).image (fun x => x * x % n)).card

theorem A123723_mem {n v : ℕ} (hn : 0 < n) :
    v ∈ (range n).image (fun x => x * x % n) ↔ ∃ x, x * x % n = v := by
  constructor
  · intro h
    obtain ⟨x, -, hx⟩ := mem_image.mp h
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    refine mem_image.mpr ⟨x % n, mem_range.mpr (Nat.mod_lt _ hn), ?_⟩
    rw [← Nat.mul_mod]

/-- Multiplicativity (Chinese remainder theorem). -/
theorem A123723_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    A123723_S (a * b) = A123723_S a * A123723_S b := by
  unfold A123723_S
  rw [← card_product]
  have hab0 : 0 < a * b := Nat.mul_pos ha hb
  have hda : a ∣ a * b := Dvd.intro b rfl
  have hdb : b ∣ a * b := Dvd.intro_left a rfl
  apply card_bij (fun v _ => (v % a, v % b))
  · intro v hv
    obtain ⟨x, rfl⟩ := (A123723_mem hab0).mp hv
    rw [mem_product, A123723_mem ha, A123723_mem hb]
    exact ⟨⟨x, (Nat.mod_mod_of_dvd _ hda).symm⟩, ⟨x, (Nat.mod_mod_of_dvd _ hdb).symm⟩⟩
  · intro v hv w hw h
    simp only [Prod.mk.injEq] at h
    have hv' : v < a * b := by
      obtain ⟨x, -, rfl⟩ := mem_image.mp hv
      exact Nat.mod_lt _ hab0
    have hw' : w < a * b := by
      obtain ⟨x, -, rfl⟩ := mem_image.mp hw
      exact Nat.mod_lt _ hab0
    have hm : v ≡ w [MOD a * b] := (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨h.1, h.2⟩
    unfold Nat.ModEq at hm
    rwa [Nat.mod_eq_of_lt hv', Nat.mod_eq_of_lt hw'] at hm
  · rintro ⟨u, u'⟩ h
    rw [mem_product, A123723_mem ha, A123723_mem hb] at h
    obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := h
    obtain ⟨z, hz1, hz2⟩ := Nat.chineseRemainder hab x y
    refine ⟨z * z % (a * b), (A123723_mem hab0).mpr ⟨z, rfl⟩, ?_⟩
    simp only [Prod.mk.injEq]
    constructor
    · rw [Nat.mod_mod_of_dvd _ hda]
      exact Nat.ModEq.mul hz1 hz1
    · rw [Nat.mod_mod_of_dvd _ hdb]
      exact Nat.ModEq.mul hz2 hz2

theorem A123723_sq_comp {m x y : ℕ} (h : x + y = m) : x * x % m = y * y % m := by
  have h1 : (x * x + x * y) % m = 0 := by
    rw [show x * x + x * y = x * m by rw [← h]; ring]
    exact Nat.mul_mod_left x m
  have h2 : (y * y + x * y) % m = 0 := by
    rw [show y * y + x * y = y * m by rw [← h]; ring]
    exact Nat.mul_mod_left y m
  exact Nat.ModEq.add_right_cancel' (x * y) (h1.trans h2.symm)

theorem A123723_half_sub {m : ℕ} :
    (range m).image (fun x => x * x % m) ⊆ (range (m / 2 + 1)).image (fun x => x * x % m) := by
  intro v hv
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
  rw [mem_range] at hx
  rcases le_or_gt x (m / 2) with h | h
  · exact mem_image.mpr ⟨x, mem_range.mpr (by omega), rfl⟩
  · exact mem_image.mpr ⟨m - x, mem_range.mpr (by omega),
      A123723_sq_comp (by omega : (m - x) + x = m)⟩

/-- x and m - x have the same square, so S(m) ≤ m/2 + 1. -/
theorem A123723_half (m : ℕ) : A123723_S m ≤ m / 2 + 1 :=
  (card_le_card A123723_half_sub).trans (card_image_le.trans (by simp))

/-- If d^2 ∣ m with d ≥ 2 then 0 and m/d have the same square, so S(m) ≤ m/2. -/
theorem A123723_half_strict {m d : ℕ} (hm : 0 < m) (hd : 2 ≤ d) (hdm : d * d ∣ m) :
    A123723_S m ≤ m / 2 := by
  obtain ⟨k, rfl⟩ := hdm
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hm
    · exact h
  set m := d * d * k with hmdef
  have hc0 : 0 < d * k := Nat.mul_pos (by omega) hk
  have hcm : d * k ≤ m / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    rw [hmdef]
    have := Nat.mul_le_mul_right (d * k) hd
    nlinarith
  have hcz : d * k * (d * k) % m = 0 := by
    rw [show d * k * (d * k) = m * k by rw [hmdef]; ring]
    exact Nat.mul_mod_right m k
  have hsub : (range m).image (fun x => x * x % m) ⊆
      ((range (m / 2 + 1)).erase (d * k)).image (fun x => x * x % m) := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := mem_image.mp (A123723_half_sub hv)
    by_cases hyc : y = d * k
    · refine mem_image.mpr ⟨0, mem_erase.mpr ⟨by omega, mem_range.mpr (by omega)⟩, ?_⟩
      rw [hyc, hcz]
      simp
    · exact mem_image.mpr ⟨y, mem_erase.mpr ⟨hyc, hy⟩, rfl⟩
  have hcard : ((range (m / 2 + 1)).erase (d * k)).card = m / 2 := by
    rw [card_erase_of_mem (mem_range.mpr (by omega)), card_range]
    omega
  calc A123723_S m ≤ (((range (m / 2 + 1)).erase (d * k)).image (fun x => x * x % m)).card :=
        card_le_card hsub
    _ ≤ m / 2 := card_image_le.trans hcard.le

theorem A123723_odd_le {m : ℕ} (hm : m % 2 = 1) : 2 * A123723_S m ≤ m + 1 := by
  have := A123723_half m
  omega

/-- 2 S(p) = p + 1 for an odd prime p. -/
theorem A123723_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 2 * A123723_S p = p + 1 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
  have hp0 : 0 < p := hp.pos
  have hinj : Set.InjOn (fun x => x * x % p) (range (p / 2 + 1) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [coe_range, Set.mem_Iio] at hx hy
    have hd : (p : ℤ) ∣ ((y * y : ℕ) : ℤ) - ((x * x : ℕ) : ℤ) := Nat.modEq_iff_dvd.mp hxy
    have hf : ((y * y : ℕ) : ℤ) - ((x * x : ℕ) : ℤ) = ((y : ℤ) - x) * ((y : ℤ) + x) := by
      push_cast
      ring
    rw [hf] at hd
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hd with h | h
    · have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
      omega
    · have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
      omega
  have hsub : (range (p / 2 + 1)).image (fun x => x * x % p) ⊆
      (range p).image (fun x => x * x % p) := by
    intro v hv
    obtain ⟨x, -, rfl⟩ := mem_image.mp hv
    exact (A123723_mem hp0).mpr ⟨x, rfl⟩
  have hlow : p / 2 + 1 ≤ A123723_S p := by
    have := card_le_card hsub
    rwa [card_image_of_injOn hinj, card_range] at this
  have := A123723_odd_le hodd
  omega

/-- For odd m, 2 S(m) = m + 1 only when m = 1 or m is prime. -/
theorem A123723_L {m : ℕ} (hm : m % 2 = 1) (h : 2 * A123723_S m = m + 1) :
    m = 1 ∨ m.Prime := by
  by_contra hc
  have h1 : m ≠ 1 := fun h => hc (Or.inl h)
  have hnp : ¬ m.Prime := fun h => hc (Or.inr h)
  have hm0 : 0 < m := by omega
  have hp : m.minFac.Prime := Nat.minFac_prime h1
  obtain ⟨b, hb⟩ := Nat.minFac_dvd m
  set p := m.minFac
  by_cases hpb : p ∣ b
  · obtain ⟨c, rfl⟩ := hpb
    have := A123723_half_strict hm0 hp.two_le ⟨c, by rw [hb]; ring⟩
    omega
  · have hcop : Nat.Coprime p b := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpb
    have hb2 : 2 ≤ b := by
      rcases b with _ | _ | b
      · simp at hb
        omega
      · simp only [zero_add, mul_one] at hb
        exact absurd (hb ▸ hp) hnp
      · omega
    have hoddpb : Odd (p * b) := by
      rw [← hb]
      exact Nat.odd_iff.mpr hm
    have hpo : p % 2 = 1 := Nat.odd_iff.mp (Nat.odd_mul.mp hoddpb).1
    have hbo : b % 2 = 1 := Nat.odd_iff.mp (Nat.odd_mul.mp hoddpb).2
    have e := A123723_mul hp.pos (by omega) hcop
    rw [← hb] at e
    have ha := A123723_odd_le hpo
    have hbb := A123723_odd_le hbo
    have hprod := Nat.mul_le_mul ha hbb
    rw [e] at h
    have hp2 := hp.two_le
    nlinarith

/-- Squares mod N reduce to squares mod M: S(N) ≤ S(M) · N/M for M ∣ N. -/
theorem A123723_res {M n : ℕ} (hM : 0 < M) (hMn : M ∣ n) :
    A123723_S n ≤ A123723_S M * (n / M) := by
  unfold A123723_S
  calc ((range n).image (fun x => x * x % n)).card
      ≤ ((((range M).image (fun x => x * x % M)) ×ˢ range (n / M)).image
          (fun q : ℕ × ℕ => q.1 + M * q.2)).card := by
        apply card_le_card
        intro v hv
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
        have hn : 0 < n := by
          rw [mem_range] at hx
          omega
        refine mem_image.mpr ⟨(x * x % n % M, x * x % n / M), mem_product.mpr ⟨?_, ?_⟩,
          Nat.mod_add_div _ M⟩
        · exact (A123723_mem hM).mpr ⟨x, (Nat.mod_mod_of_dvd _ hMn).symm⟩
        · exact mem_range.mpr (Nat.div_lt_div_of_lt_of_dvd hMn (Nat.mod_lt _ hn))
    _ ≤ (((range M).image (fun x => x * x % M)) ×ˢ range (n / M)).card := card_image_le
    _ = ((range M).image (fun x => x * x % M)).card * (n / M) := by
        rw [card_product, card_range]

theorem A123723_S1 : A123723_S 1 = 1 := by decide
theorem A123723_S4 : A123723_S 4 = 2 := by decide
theorem A123723_S8 : A123723_S 8 = 3 := by decide
theorem A123723_S16 : A123723_S 16 = 4 := by decide
theorem A123723_S32 : A123723_S 32 = 7 := by decide

theorem A123723_two_pow_upper8 (k : ℕ) : A123723_S (2 ^ (k + 3)) ≤ 3 * 2 ^ k := by
  have h := A123723_res (M := 8) (n := 2 ^ (k + 3)) (by norm_num) ⟨2 ^ k, by ring⟩
  have hd : 2 ^ (k + 3) / 8 = 2 ^ k := by
    rw [show 2 ^ (k + 3) = 8 * 2 ^ k by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  rwa [A123723_S8, hd] at h

theorem A123723_two_pow_upper32 (k : ℕ) : A123723_S (2 ^ (k + 5)) ≤ 7 * 2 ^ k := by
  have h := A123723_res (M := 32) (n := 2 ^ (k + 5)) (by norm_num) ⟨2 ^ k, by ring⟩
  have hd : 2 ^ (k + 5) / 32 = 2 ^ k := by
    rw [show 2 ^ (k + 5) = 32 * 2 ^ k by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  rwa [A123723_S32, hd] at h

/-- Classification: if 4 ∣ N, N ≠ 4 and S(N) = N/4 + 1 then N/4 is prime. -/
theorem A123723_classify {n : ℕ} (hn : 0 < n) (h4 : 4 ∣ n) (hS : A123723_S n = n / 4 + 1)
    (hne : n ≠ 4) : (n / 4).Prime := by
  obtain ⟨j, r, hr2, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 2 (by norm_num)
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with rfl | h
    · simp at hn
    · exact h
  have hro : r % 2 = 1 := by omega
  have hcop : Nat.Coprime (2 ^ j) r :=
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hr2)
  have hmul := A123723_mul (pow_pos (by norm_num : 0 < 2) j) hr0 hcop
  rw [hmul] at hS
  have hodd := A123723_odd_le hro
  rcases j with _ | _ | _ | _ | j
  · simp only [pow_zero, one_mul] at h4
    omega
  · simp only [zero_add, pow_one] at h4
    omega
  · have hdiv : 2 ^ (0 + 1 + 1) * r / 4 = r := by
      rw [show 2 ^ (0 + 1 + 1) * r = 4 * r by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hdiv] at hS ⊢
    rw [show 2 ^ (0 + 1 + 1) = 4 by norm_num, A123723_S4] at hS
    rcases A123723_L hro hS with h | h
    · subst h
      simp at hne
    · exact h
  · have hdiv : 2 ^ (0 + 1 + 1 + 1) * r / 4 = 2 * r := by
      rw [show 2 ^ (0 + 1 + 1 + 1) * r = 4 * (2 * r) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hdiv] at hS ⊢
    rw [show 2 ^ (0 + 1 + 1 + 1) = 8 by norm_num, A123723_S8] at hS
    have hr1 : r = 1 := by omega
    subst hr1
    norm_num
  · have hdiv : 2 ^ (j + 1 + 1 + 1 + 1) * r / 4 = 4 * 2 ^ j * r := by
      rw [show 2 ^ (j + 1 + 1 + 1 + 1) * r = 4 * (4 * 2 ^ j * r) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hdiv] at hS
    exfalso
    have hX : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by norm_num)
    rcases (show r = 1 ∨ 3 ≤ r by omega) with rfl | hr3
    · rw [A123723_S1, mul_one, mul_one] at hS
      rcases j with _ | j
      · rw [show 2 ^ (0 + 1 + 1 + 1 + 1) = 16 by norm_num, A123723_S16] at hS
        simp at hS
      · have := A123723_two_pow_upper32 j
        rw [show 2 ^ (j + 1 + 1 + 1 + 1 + 1) = 2 ^ (j + 5) by ring,
          show 4 * 2 ^ (j + 1) = 8 * 2 ^ j by ring] at hS
        omega
    · have hub := A123723_two_pow_upper8 (j + 1)
      rw [show j + 1 + 1 + 1 + 1 = j + 1 + 3 by ring] at hS
      have hprod := Nat.mul_le_mul hub hodd
      have h3 := Nat.mul_le_mul_left (2 ^ j) hr3
      rw [show 2 ^ (j + 1) = 2 * 2 ^ j by ring] at hprod
      nlinarith

/-- 4p is a member for every odd prime p. -/
theorem A123723_four_mul_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    A123723_S (4 * p) = 4 * p / 4 + 1 := by
  rw [Nat.mul_div_cancel_left _ (by norm_num)]
  have hcop : Nat.Coprime 4 p := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm h2))
  rw [A123723_mul (by norm_num) hp.pos hcop, A123723_S4]
  have := A123723_prime hp h2
  omega

/-- Membership predicate of A123723. -/
def A123723_P (N : ℕ) : Prop := 0 < N ∧ A123723_S N = N / 4 + 1

instance : DecidablePred A123723_P := fun N =>
  inferInstanceAs (Decidable (0 < N ∧ A123723_S N = N / 4 + 1))

/-- a(n), offset 1. -/
noncomputable def A123723_a (n : ℕ) : ℕ := Nat.nth A123723_P (n - 1)

theorem A123723_data :
    (List.range 64).filter (fun N => decide (A123723_P N)) =
      [1, 4, 8, 12, 20, 28, 44, 45, 52, 63] := by
  decide +kernel

theorem A123723_infinite : (Set.ofPred A123723_P).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hpa, hp⟩ := Nat.exists_infinite_primes (a + 3)
  refine ⟨4 * p, (⟨by have := hp.pos; omega, A123723_four_mul_prime hp (by omega)⟩ :
    A123723_P (4 * p)), by omega⟩

theorem A123723_main : ∀ n, 4 < n → 4 ∣ A123723_a n → (A123723_a n / 4).Prime := by
  intro n hn h4
  have hmem := Nat.nth_mem_of_infinite A123723_infinite (n - 1)
  have h3 : Nat.nth A123723_P 3 = 12 := by
    have h := Nat.nth_count (p := A123723_P) (n := 12) (by decide)
    rwa [show Nat.count A123723_P 12 = 3 by decide] at h
  have hgt : Nat.nth A123723_P 3 < Nat.nth A123723_P (n - 1) :=
    Nat.nth_strictMono A123723_infinite (by omega)
  rw [h3] at hgt
  exact A123723_classify hmem.1 h4 hmem.2 (by unfold A123723_a; omega)
