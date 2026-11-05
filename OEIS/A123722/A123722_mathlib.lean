/-
OEIS A123722, Mathlib proof of J. W. Layman's conjecture (2006).

A000224(n) = number of squares mod n = `A123722_S n` = #{x^2 mod n : 0 ≤ x < n}.
A123722 lists the n ≥ 1 with A000224(n) = ⌈(n+1)/3⌉; in ℕ, ⌈(n+1)/3⌉ = n/3 + 1
(`A123722_P`). a(n) = `Nat.nth A123722_P (n - 1)` (offset 1).

Main theorem `A123722_main`:
  (1) for every n > 2, if 3 ∣ a(n) then a(n)/3 is prime;
  (2) for every odd prime p there is n ≥ 1 with a(n) = 3p.
`A123722_classify`: for N > 0 with 3 ∣ N, N ≠ 3 and S(N) = N/3 + 1, N/3 is prime.
`A123722_data`: the members below 40 are 1, 3, 4, 8, 9, 15, 21, 33, 35, 39 (OEIS data).

Proof. S is multiplicative on coprime arguments (CRT, `A123722_mul`); S(m) ≤ m/2 + 1
(x and m - x have the same square, `A123722_half`), and S(m) ≤ m/2 when d^2 ∣ m for some d ≥ 2
(0 and m/d have the same square, `A123722_half_strict`); 2S(p) = p + 1 for odd primes p
(`A123722_prime`). Hence for odd m, 2S(m) = m + 1 forces m = 1 or m prime (`A123722_L`).
S(N) ≤ S(M)·N/M for M ∣ N (squares mod N reduce to squares mod M, `A123722_res`), so
S(3^k) ≤ 4·3^(k-2). Squaring is injective on {3j + 1 : j < 3^(k-1)} mod 3^k, so
S(3^k) ≥ 3^(k-1) + 2 for k ≥ 3 (`A123722_three_pow_lower`). Write N = 3^k r with 3 ∤ r:
k = 1 gives 2S(r) = r + 1 (r odd by parity, then `A123722_L`); k ≥ 2 is impossible except
N = 9 (r ≥ 4 by the size bounds, r = 2 by parity, r = 1 by the lower bound).

Not checked in Lean: nothing for the statement above.
-/
import Mathlib

open Finset

/-- The number of squares mod n (A000224); `A123722_S 0 = 0`. -/
def A123722_S (n : ℕ) : ℕ := ((range n).image (fun x => x * x % n)).card

theorem A123722_mem {n v : ℕ} (hn : 0 < n) :
    v ∈ (range n).image (fun x => x * x % n) ↔ ∃ x, x * x % n = v := by
  constructor
  · intro h
    obtain ⟨x, -, hx⟩ := mem_image.mp h
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    refine mem_image.mpr ⟨x % n, mem_range.mpr (Nat.mod_lt _ hn), ?_⟩
    rw [← Nat.mul_mod]

/-- Multiplicativity (Chinese remainder theorem). -/
theorem A123722_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    A123722_S (a * b) = A123722_S a * A123722_S b := by
  unfold A123722_S
  rw [← card_product]
  have hab0 : 0 < a * b := Nat.mul_pos ha hb
  have hda : a ∣ a * b := Dvd.intro b rfl
  have hdb : b ∣ a * b := Dvd.intro_left a rfl
  apply card_bij (fun v _ => (v % a, v % b))
  · intro v hv
    obtain ⟨x, rfl⟩ := (A123722_mem hab0).mp hv
    rw [mem_product, A123722_mem ha, A123722_mem hb]
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
    rw [mem_product, A123722_mem ha, A123722_mem hb] at h
    obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := h
    obtain ⟨z, hz1, hz2⟩ := Nat.chineseRemainder hab x y
    refine ⟨z * z % (a * b), (A123722_mem hab0).mpr ⟨z, rfl⟩, ?_⟩
    simp only [Prod.mk.injEq]
    constructor
    · rw [Nat.mod_mod_of_dvd _ hda]
      exact Nat.ModEq.mul hz1 hz1
    · rw [Nat.mod_mod_of_dvd _ hdb]
      exact Nat.ModEq.mul hz2 hz2

theorem A123722_sq_comp {m x y : ℕ} (h : x + y = m) : x * x % m = y * y % m := by
  have h1 : (x * x + x * y) % m = 0 := by
    rw [show x * x + x * y = x * m by rw [← h]; ring]
    exact Nat.mul_mod_left x m
  have h2 : (y * y + x * y) % m = 0 := by
    rw [show y * y + x * y = y * m by rw [← h]; ring]
    exact Nat.mul_mod_left y m
  exact Nat.ModEq.add_right_cancel' (x * y) (h1.trans h2.symm)

theorem A123722_half_sub {m : ℕ} :
    (range m).image (fun x => x * x % m) ⊆ (range (m / 2 + 1)).image (fun x => x * x % m) := by
  intro v hv
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
  rw [mem_range] at hx
  rcases le_or_gt x (m / 2) with h | h
  · exact mem_image.mpr ⟨x, mem_range.mpr (by omega), rfl⟩
  · exact mem_image.mpr ⟨m - x, mem_range.mpr (by omega),
      A123722_sq_comp (by omega : (m - x) + x = m)⟩

/-- x and m - x have the same square, so S(m) ≤ m/2 + 1. -/
theorem A123722_half (m : ℕ) : A123722_S m ≤ m / 2 + 1 :=
  (card_le_card A123722_half_sub).trans (card_image_le.trans (by simp))

/-- If d^2 ∣ m with d ≥ 2 then 0 and m/d have the same square, so S(m) ≤ m/2. -/
theorem A123722_half_strict {m d : ℕ} (hm : 0 < m) (hd : 2 ≤ d) (hdm : d * d ∣ m) :
    A123722_S m ≤ m / 2 := by
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
    obtain ⟨y, hy, rfl⟩ := mem_image.mp (A123722_half_sub hv)
    by_cases hyc : y = d * k
    · refine mem_image.mpr ⟨0, mem_erase.mpr ⟨by omega, mem_range.mpr (by omega)⟩, ?_⟩
      rw [hyc, hcz]
      simp
    · exact mem_image.mpr ⟨y, mem_erase.mpr ⟨hyc, hy⟩, rfl⟩
  have hcard : ((range (m / 2 + 1)).erase (d * k)).card = m / 2 := by
    rw [card_erase_of_mem (mem_range.mpr (by omega)), card_range]
    omega
  calc A123722_S m ≤ (((range (m / 2 + 1)).erase (d * k)).image (fun x => x * x % m)).card :=
        card_le_card hsub
    _ ≤ m / 2 := card_image_le.trans hcard.le

theorem A123722_odd_le {m : ℕ} (hm : m % 2 = 1) : 2 * A123722_S m ≤ m + 1 := by
  have := A123722_half m
  omega

/-- 2 S(p) = p + 1 for an odd prime p. -/
theorem A123722_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 2 * A123722_S p = p + 1 := by
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
    exact (A123722_mem hp0).mpr ⟨x, rfl⟩
  have hlow : p / 2 + 1 ≤ A123722_S p := by
    have := card_le_card hsub
    rwa [card_image_of_injOn hinj, card_range] at this
  have := A123722_odd_le hodd
  omega

/-- For odd m, 2 S(m) = m + 1 only when m = 1 or m is prime. -/
theorem A123722_L {m : ℕ} (hm : m % 2 = 1) (h : 2 * A123722_S m = m + 1) :
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
    have := A123722_half_strict hm0 hp.two_le ⟨c, by rw [hb]; ring⟩
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
    have e := A123722_mul hp.pos (by omega) hcop
    rw [← hb] at e
    have ha := A123722_odd_le hpo
    have hbb := A123722_odd_le hbo
    have hprod := Nat.mul_le_mul ha hbb
    rw [e] at h
    have hp2 := hp.two_le
    nlinarith

/-- Squares mod N reduce to squares mod M: S(N) ≤ S(M) · N/M for M ∣ N. -/
theorem A123722_res {M n : ℕ} (hM : 0 < M) (hMn : M ∣ n) :
    A123722_S n ≤ A123722_S M * (n / M) := by
  unfold A123722_S
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
        · exact (A123722_mem hM).mpr ⟨x, (Nat.mod_mod_of_dvd _ hMn).symm⟩
        · exact mem_range.mpr (Nat.div_lt_div_of_lt_of_dvd hMn (Nat.mod_lt _ hn))
    _ ≤ (((range M).image (fun x => x * x % M)) ×ˢ range (n / M)).card := card_image_le
    _ = ((range M).image (fun x => x * x % M)).card * (n / M) := by
        rw [card_product, card_range]

theorem A123722_S1 : A123722_S 1 = 1 := by decide
theorem A123722_S2 : A123722_S 2 = 2 := by decide
theorem A123722_S3 : A123722_S 3 = 2 := by decide
theorem A123722_S9 : A123722_S 9 = 4 := by decide

theorem A123722_three_pow_upper (k : ℕ) : A123722_S (3 ^ (k + 2)) ≤ 4 * 3 ^ k := by
  have h := A123722_res (M := 9) (n := 3 ^ (k + 2)) (by norm_num) ⟨3 ^ k, by ring⟩
  have hd : 3 ^ (k + 2) / 9 = 3 ^ k := by
    rw [show 3 ^ (k + 2) = 9 * 3 ^ k by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  rwa [A123722_S9, hd] at h

/-- Squaring is injective on 3j + 1 (j < 3^(k-1)) mod 3^k; with 0 and 9, S(3^k) ≥ 3^(k-1) + 2. -/
theorem A123722_three_pow_lower (k : ℕ) : 3 ^ (k + 2) + 2 ≤ A123722_S (3 ^ (k + 3)) := by
  set N := 3 ^ (k + 2) with hN
  set Q := 3 ^ (k + 3) with hQ
  have hQN : Q = 3 * N := by rw [hQ, hN]; ring
  have hQ27 : 27 ≤ Q := by
    rw [hQ, show 3 ^ (k + 3) = 27 * 3 ^ k by ring]
    have : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hQ0 : 0 < Q := by omega
  set B := (range N).image (fun j => (3 * j + 1) * (3 * j + 1) % Q) with hB
  have hBcard : B.card = N := by
    rw [hB, card_image_of_injOn, card_range]
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    have hd : (Q : ℤ) ∣ (((3 * j + 1) * (3 * j + 1) : ℕ) : ℤ) - (((3 * i + 1) * (3 * i + 1) : ℕ) : ℤ) :=
      Nat.modEq_iff_dvd.mp hij
    have hf : (((3 * j + 1) * (3 * j + 1) : ℕ) : ℤ) - (((3 * i + 1) * (3 * i + 1) : ℕ) : ℤ) =
        (3 * ((j : ℤ) - i)) * (3 * ((i : ℤ) + j) + 2) := by
      push_cast
      ring
    rw [hf] at hd
    have hcop : IsCoprime (Q : ℤ) (3 * ((i : ℤ) + j) + 2) := by
      rw [hQ]
      push_cast
      apply IsCoprime.pow_left
      exact ⟨(i : ℤ) + j + 1, -1, by ring⟩
    have h2 := hcop.dvd_of_dvd_mul_right hd
    rw [hQN] at h2
    push_cast at h2
    have h3 : (N : ℤ) ∣ (j : ℤ) - i := (mul_dvd_mul_iff_left (by norm_num)).mp h2
    have := Int.eq_zero_of_abs_lt_dvd h3 (by rw [abs_lt]; constructor <;> omega)
    omega
  have hmod3 : ∀ v ∈ B, v % 3 = 1 := by
    intro v hv
    obtain ⟨j, -, rfl⟩ := mem_image.mp hv
    rw [Nat.mod_mod_of_dvd _ (⟨N, hQN⟩ : 3 ∣ Q)]
    rw [show (3 * j + 1) * (3 * j + 1) = 3 * (3 * j * j + 2 * j) + 1 by ring]
    generalize 3 * j * j + 2 * j = t
    omega
  have h0 : (0 : ℕ) ∉ insert 9 B := by
    rw [mem_insert]
    rintro (h | h)
    · omega
    · have := hmod3 0 h
      omega
  have h9 : (9 : ℕ) ∉ B := by
    intro h
    have := hmod3 9 h
    omega
  have hsub : insert 0 (insert 9 B) ⊆ (range Q).image (fun x => x * x % Q) := by
    intro v hv
    rw [mem_insert, mem_insert] at hv
    rw [A123722_mem hQ0]
    rcases hv with rfl | rfl | hv
    · exact ⟨0, by simp⟩
    · exact ⟨3, Nat.mod_eq_of_lt (by omega)⟩
    · obtain ⟨j, -, rfl⟩ := mem_image.mp hv
      exact ⟨3 * j + 1, rfl⟩
  have := card_le_card hsub
  rw [card_insert_of_notMem h0, card_insert_of_notMem h9, hBcard] at this
  exact this

theorem A123722_coprime3 {r : ℕ} (hr : ¬ 3 ∣ r) (j : ℕ) : Nat.Coprime (3 ^ j) r :=
  Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hr)

/-- Classification: if 3 ∣ N, N ≠ 3 and S(N) = N/3 + 1 then N/3 is prime. -/
theorem A123722_classify {n : ℕ} (hn : 0 < n) (h3 : 3 ∣ n) (hS : A123722_S n = n / 3 + 1)
    (hne : n ≠ 3) : (n / 3).Prime := by
  obtain ⟨k, r, hr3, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 3 (by norm_num)
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with rfl | h
    · simp at hn
    · exact h
  have hmul := A123722_mul (pow_pos (by norm_num : 0 < 3) k) hr0 (A123722_coprime3 hr3 k)
  rw [hmul] at hS
  rcases k with _ | _ | k
  · simp only [pow_zero, one_mul] at h3
    exact absurd h3 hr3
  · simp only [zero_add, pow_one] at hS hne ⊢
    rw [A123722_S3, Nat.mul_div_cancel_left _ (by norm_num)] at hS
    rw [Nat.mul_div_cancel_left _ (by norm_num)]
    have hodd : r % 2 = 1 := by omega
    rcases A123722_L hodd hS with h | h
    · subst h
      simp at hne
    · exact h
  · have hdiv : 3 ^ (k + 1 + 1) * r / 3 = 3 * 3 ^ k * r := by
      rw [show 3 ^ (k + 1 + 1) * r = 3 * (3 * 3 ^ k * r) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hdiv] at hS ⊢
    have hX : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    rcases (show r = 1 ∨ r = 2 ∨ 4 ≤ r by omega) with rfl | rfl | hr4
    · rw [A123722_S1, mul_one, mul_one] at hS
      rcases k with _ | k
      · norm_num
      · have := A123722_three_pow_lower k
        rw [show 3 ^ (k + 1 + 1 + 1) = 3 ^ (k + 3) by ring,
          show 3 * 3 ^ (k + 1) = 3 ^ (k + 2) by ring] at hS
        omega
    · rw [A123722_S2] at hS
      omega
    · have hub := A123722_three_pow_upper k
      rw [show k + 1 + 1 = k + 2 by ring] at hS
      have hh := A123722_half r
      have h2 : 2 * A123722_S r ≤ r + 2 := by omega
      have hprod := Nat.mul_le_mul hub h2
      have h4 := Nat.mul_le_mul_left (3 ^ k) hr4
      nlinarith

/-- 3p is a member for every odd prime p. -/
theorem A123722_three_mul_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    A123722_S (3 * p) = 3 * p / 3 + 1 := by
  rw [Nat.mul_div_cancel_left _ (by norm_num)]
  by_cases h3 : p = 3
  · subst h3
    decide
  · have hcop : Nat.Coprime 3 p :=
      (Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm h3)
    rw [A123722_mul (by norm_num) hp.pos hcop, A123722_S3]
    have := A123722_prime hp h2
    omega

/-- Membership predicate of A123722. -/
def A123722_P (N : ℕ) : Prop := 0 < N ∧ A123722_S N = N / 3 + 1

instance : DecidablePred A123722_P := fun N =>
  inferInstanceAs (Decidable (0 < N ∧ A123722_S N = N / 3 + 1))

/-- a(n), offset 1. -/
noncomputable def A123722_a (n : ℕ) : ℕ := Nat.nth A123722_P (n - 1)

theorem A123722_data :
    (List.range 40).filter (fun N => decide (A123722_P N)) = [1, 3, 4, 8, 9, 15, 21, 33, 35, 39] := by
  decide

theorem A123722_infinite : (Set.ofPred A123722_P).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hpa, hp⟩ := Nat.exists_infinite_primes (a + 3)
  refine ⟨3 * p, (⟨by have := hp.pos; omega, A123722_three_mul_prime hp (by omega)⟩ :
    A123722_P (3 * p)), by omega⟩

theorem A123722_main :
    (∀ n, 2 < n → 3 ∣ A123722_a n → (A123722_a n / 3).Prime) ∧
    (∀ p, p.Prime → p ≠ 2 → ∃ n, 1 ≤ n ∧ A123722_a n = 3 * p) := by
  constructor
  · intro n hn h3
    have hmem := Nat.nth_mem_of_infinite A123722_infinite (n - 1)
    have h1 : Nat.nth A123722_P 1 = 3 := by
      have h := Nat.nth_count (p := A123722_P) (n := 3) (by decide)
      rwa [show Nat.count A123722_P 3 = 1 by decide] at h
    have hgt : Nat.nth A123722_P 1 < Nat.nth A123722_P (n - 1) :=
      Nat.nth_strictMono A123722_infinite (by omega)
    rw [h1] at hgt
    exact A123722_classify hmem.1 h3 hmem.2 (by unfold A123722_a; omega)
  · intro p hp h2
    have hP : A123722_P (3 * p) := ⟨by have := hp.pos; omega, A123722_three_mul_prime hp h2⟩
    refine ⟨Nat.count A123722_P (3 * p) + 1, by omega, ?_⟩
    unfold A123722_a
    simpa using Nat.nth_count hP
