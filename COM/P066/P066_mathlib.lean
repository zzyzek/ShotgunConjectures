import Mathlib

/-
COM-P066, part 1 (= Coman's conjecture 126): every Poulet number P with 3, 5 not
dividing P has some m >= 1 with (P + 5^m)/6^n a prime or a prime power.
False, non-constructively.

Checked here, for every P = a (mod M) (a, M below, gcd(a, M) = 1), every m >= 0
and every n with 6^n | P + 5^m: (P + 5^m)/6^n is not a prime power (in
particular not prime).  `P066_part1`.
Route.
* P = 1 (mod 4) makes P + 5^m = 2 (mod 4), so n <= 1 (`not_four_dvd`).
* n = 0: P + 5^m = 2 * (odd number > 1), divisible by two coprime numbers > 1.
* n = 1: then 3 | P + 5^m, so m is odd (P = 1 mod 3).  Two disjoint coverings
  of the odd m, `cover1` (classes mod 16, primes 13, 313, 17, 11489) and
  `cover2` (classes mod 144, primes 31, 7, 601, 390001, 19, 829, 5167), give
  coprime q1, q2 > 1 dividing (P + 5^m)/6 (`cover_dvd`).
* A number with two coprime divisors > 1 is not a prime power (`not_isPrimePow`).
* `class_facts`: a = 1 (mod 12), a = 1 (mod 5), gcd(a, M) = 1.
Not checked here: that the class contains Poulet numbers.  It is a coprime
residue class, so it contains infinitely many Carmichael numbers by T. Wright,
Infinitely many Carmichael numbers in arithmetic progressions, Bull. London
Math. Soc. 45 (2013) 943-952; Carmichael numbers are Poulet numbers, and these
have 3, 5 not dividing P.  No explicit P is known.
-/

def a : ℕ := 164743819436130905311195649881
def M : ℕ := 197386120142055051194076523980

def cover1 : List (ℕ × ℕ × ℕ) := [(13, 4, 1), (313, 8, 3), (17, 16, 7), (11489, 16, 15)]
def cover2 : List (ℕ × ℕ × ℕ) :=
  [(31, 3, 0), (7, 6, 1), (601, 12, 5), (390001, 24, 11), (19, 9, 2), (829, 9, 5), (5167, 18, 17)]

theorem M_eq : M = 4 * 3 * 5 * 13 * 313 * 17 * 11489 * 31 * 7 * 601 * 390001 * 19 * 829 * 5167 := by
  decide
theorem class_facts : a % 12 = 1 ∧ a % 5 = 1 ∧ Nat.gcd a M = 1 := by decide

theorem pow_period (b q o n : ℕ) (ho : b ^ o % q = 1) : b ^ n % q = b ^ (n % o) % q := by
  have h := Nat.div_add_mod n o
  conv => lhs; rw [← h, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, ho, Nat.one_pow]
  have hq : q ≠ 1 := by
    intro h1; rw [h1, Nat.mod_one] at ho; exact absurd ho (by decide)
  cases q with
  | zero => simp
  | succ q' =>
    have : 1 % (q' + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.one_mul, Nat.mod_mod]

theorem P_mod (P d : ℕ) (hP : P % M = a) (hd : M % d = 0) : P % d = a % d := by
  rw [← Nat.mod_mod_of_dvd P (Nat.dvd_of_mod_eq_zero hd), hP]

/-- A covering of the odd residues mod L gives a divisor of P + 5^m for odd m. -/
theorem cover_dvd (cov : List (ℕ × ℕ × ℕ)) (L : ℕ) (hL2 : 2 ∣ L)
    (hodd : (List.range L).all (fun r => r % 2 == 0 || cov.any (fun t => r % t.2.1 == t.2.2)) = true)
    (hord : cov.all (fun t => 5 ^ t.2.1 % t.1 == 1) = true)
    (hcls : cov.all (fun t => (a + 5 ^ t.2.2) % t.1 == 0) = true)
    (hper : cov.all (fun t => L % t.2.1 == 0 && M % t.1 == 0) = true)
    (P m : ℕ) (hP : P % M = a) (hm : m % 2 = 1) (hL : 0 < L) :
    ∃ t ∈ cov, t.1 ∣ P + 5 ^ m := by
  have hr : m % L ∈ List.range L := List.mem_range.mpr (Nat.mod_lt _ hL)
  have h1 := List.all_eq_true.mp hodd _ hr
  have hmL : m % L % 2 = 1 := by rw [Nat.mod_mod_of_dvd m hL2]; exact hm
  simp only [hmL, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (by decide)
  obtain ⟨t, ht, hc⟩ := List.any_eq_true.mp h1
  have ho : 5 ^ t.2.1 % t.1 = 1 := by simpa using List.all_eq_true.mp hord t ht
  have hc2 : (a + 5 ^ t.2.2) % t.1 = 0 := by simpa using List.all_eq_true.mp hcls t ht
  have hp := List.all_eq_true.mp hper t ht
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨hdL, hdM⟩ := hp
  have hcl : m % L % t.2.1 = t.2.2 := by simpa using hc
  have hn : m % t.2.1 = t.2.2 := by
    rw [← Nat.mod_mod_of_dvd m (Nat.dvd_of_mod_eq_zero hdL)]; exact hcl
  refine ⟨t, ht, Nat.dvd_of_mod_eq_zero ?_⟩
  rw [Nat.add_mod, P_mod P t.1 hP hdM, pow_period 5 t.1 t.2.1 m ho, hn, ← Nat.add_mod, hc2]

theorem not_isPrimePow (V x y : ℕ) (hx : 1 < x) (hy : 1 < y) (hxy : Nat.gcd x y = 1)
    (hxV : x ∣ V) (hyV : y ∣ V) : ¬ IsPrimePow V := by
  rw [isPrimePow_nat_iff]
  rintro ⟨p, k, hp, _, rfl⟩
  have hdiv : ∀ z, 1 < z → z ∣ p ^ k → p ∣ z := by
    intro z hz hzV
    obtain ⟨i, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hzV
    rcases i with _ | i
    · simp at hz
    · exact dvd_pow_self p (Nat.succ_ne_zero i)
  have h := Nat.dvd_gcd (hdiv x hx hxV) (hdiv y hy hyV)
  rw [hxy] at h
  exact hp.one_lt.ne' (Nat.dvd_one.mp h)

theorem cover1_ok : (List.range 16).all
    (fun r => r % 2 == 0 || cover1.any (fun t => r % t.2.1 == t.2.2)) = true := by decide
theorem cover2_ok : (List.range 144).all
    (fun r => r % 2 == 0 || cover2.any (fun t => r % t.2.1 == t.2.2)) = true := by decide
theorem ord1 : cover1.all (fun t => 5 ^ t.2.1 % t.1 == 1) = true := by decide
theorem ord2 : cover2.all (fun t => 5 ^ t.2.1 % t.1 == 1) = true := by decide
theorem cls1 : cover1.all (fun t => (a + 5 ^ t.2.2) % t.1 == 0) = true := by decide
theorem cls2 : cover2.all (fun t => (a + 5 ^ t.2.2) % t.1 == 0) = true := by decide
theorem per1 : cover1.all (fun t => 16 % t.2.1 == 0 && M % t.1 == 0) = true := by decide
theorem per2 : cover2.all (fun t => 144 % t.2.1 == 0 && M % t.1 == 0) = true := by decide
theorem small : (cover1 ++ cover2).all (fun t => decide (1 < t.1) && Nat.gcd 6 t.1 == 1) = true := by
  decide
theorem disjoint : cover1.all (fun t => cover2.all (fun u => Nat.gcd t.1 u.1 == 1)) = true := by
  decide

theorem P066_part1 (P m n : ℕ) (hP : P % M = a) (hn : 6 ^ n ∣ P + 5 ^ m) :
    ¬ IsPrimePow ((P + 5 ^ m) / 6 ^ n) := by
  have hP4 : P % 4 = 1 := by rw [P_mod P 4 hP (by decide)]; decide
  have hP3 : P % 3 = 1 := by rw [P_mod P 3 hP (by decide)]; decide
  have hPa : a ≤ P := by rw [← hP]; exact Nat.mod_le P M
  have h54 : 5 ^ m % 4 = 1 := by rw [pow_period 5 4 1 m (by decide), Nat.mod_one, pow_zero]; decide
  have hX4 : (P + 5 ^ m) % 4 = 2 := by omega
  have hn1 : n ≤ 1 := by
    by_contra h
    have h36 : 6 ^ 2 ∣ 6 ^ n := Nat.pow_dvd_pow 6 (by omega)
    have := Nat.dvd_trans (Nat.dvd_trans (by decide : 4 ∣ 6 ^ 2) h36) hn
    omega
  have hP4' : 4 ≤ P := le_trans (by decide : 4 ≤ a) hPa
  obtain ⟨X, hX⟩ : ∃ X, X = P + 5 ^ m := ⟨_, rfl⟩
  rw [← hX] at hX4 hn ⊢
  have hXge : 4 ≤ X := by rw [hX]; exact le_trans hP4' (Nat.le_add_right _ _)
  rcases Nat.lt_or_ge n 1 with h0 | h1
  · have hn0 : n = 0 := by omega
    subst hn0
    rw [pow_zero, Nat.div_one]
    have hy : (X / 2) % 2 = 1 := by omega
    have hy1 : 1 < X / 2 := by omega
    apply not_isPrimePow _ 2 (X / 2) (by decide) hy1
    · rw [Nat.gcd_rec, hy, Nat.gcd_one_left]
    · exact Nat.dvd_of_mod_eq_zero (by omega)
    · exact Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero (by omega))
  · have hn1' : n = 1 := by omega
    subst hn1'
    rw [pow_one] at hn ⊢
    have hmo : m % 2 = 1 := by
      by_contra hme
      have h53 : 5 ^ m % 3 = 1 := by
        rw [pow_period 5 3 2 m (by decide), show m % 2 = 0 by omega]; decide
      have := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (by decide : 3 ∣ 6) hn)
      omega
    obtain ⟨t, ht, htd⟩ := cover_dvd cover1 16 (by decide) cover1_ok ord1 cls1 per1 P m hP hmo
      (by decide)
    obtain ⟨u, hu, hud⟩ := cover_dvd cover2 144 (by decide) cover2_ok ord2 cls2 per2 P m hP hmo
      (by decide)
    rw [← hX] at htd hud
    have hs := List.all_eq_true.mp small
    have ht' := hs t (List.mem_append_left _ ht)
    have hu' := hs u (List.mem_append_right _ hu)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ht' hu'
    have hg : Nat.gcd t.1 u.1 = 1 := by
      have := List.all_eq_true.mp (List.all_eq_true.mp disjoint t ht) u hu
      simpa using this
    apply not_isPrimePow _ t.1 u.1 ht'.1 hu'.1 hg
    · exact Nat.dvd_div_of_mul_dvd (Nat.Coprime.mul_dvd_of_dvd_of_dvd ht'.2 hn htd)
    · exact Nat.dvd_div_of_mul_dvd (Nat.Coprime.mul_dvd_of_dvd_of_dvd hu'.2 hn hud)
