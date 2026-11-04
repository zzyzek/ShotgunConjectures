/-
OEIS A135571, Mathlib proof.

A135571: positive integers that are the difference of two positive
triangular numbers in an odd number of ways. Conjecture: these are exactly
the positive integers that are a square, twice a square, or triangular, but
not both a square and triangular.

Definitions: T(a) = a(a+1)/2; a way of writing n is a pair (a, b) with
1 ≤ b < a and T(a) - T(b) = n, i.e. a(a+1) = b(b+1) + 2n (`A135571_reps n`;
every such pair has a ≤ n, `A135571_bound`, so the finset over [0, n]² holds
all of them). `A135571_tri n`: n = k(k+1)/2 for some k.

Main theorem `A135571_main`: for every n ≥ 1,
  Odd #(A135571_reps n) ↔
    (IsSquare n ∨ (∃ m, n = 2 m²) ∨ A135571_tri n) ∧ ¬ (IsSquare n ∧ A135571_tri n).
This is the README result.

Proof: the pairs with 0 ≤ b < a correspond to the odd divisors of n
(the odd one of a - b, a + b + 1, whose product is 2n); b = 0 happens once
iff n is triangular; the number of odd divisors of n = 2^k·m (m odd) is the
number of divisors of m, odd iff m is a square iff n is a square or twice a
square; a twice-square is never triangular. Nothing is outside Lean.
-/
import Mathlib

/-- n is triangular: n = k(k+1)/2. -/
def A135571_tri (n : ℕ) : Prop := ∃ k : ℕ, 2 * n = k * (k + 1)

/-- Pairs (a, b), 0 ≤ b < a ≤ n, with a(a+1) = b(b+1) + 2n. -/
def A135571_reps0 (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun p => p.2 < p.1 ∧ p.1 * (p.1 + 1) = p.2 * (p.2 + 1) + 2 * n)

/-- Ways of writing n as T(a) - T(b) with T(b) positive: 1 ≤ b < a. -/
def A135571_reps (n : ℕ) : Finset (ℕ × ℕ) := (A135571_reps0 n).filter (fun p => 1 ≤ p.2)

theorem A135571_bound (n a b : ℕ) (hab : b < a) (h : a * (a + 1) = b * (b + 1) + 2 * n) :
    a ≤ n := by
  /- a(a+1) - (a-1)a = 2a ≤ 2n -/
  have hb : b + 1 ≤ a := hab
  have : b * (b + 1) + 2 * a ≤ a * (a + 1) := by
    have : b * (b + 1) ≤ (a - 1) * a := Nat.mul_le_mul (by omega) (by omega)
    have e : (a - 1) * a + 2 * a = a * (a + 1) := by
      obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    omega
  omega

/-! ### Pairs and odd divisors -/

/-- The odd one of a - b and a + b + 1. -/
def A135571_odd (p : ℕ × ℕ) : ℕ := if (p.1 - p.2) % 2 = 1 then p.1 - p.2 else p.1 + p.2 + 1

theorem A135571_prod (a b n : ℕ) (hab : b < a) (h : a * (a + 1) = b * (b + 1) + 2 * n) :
    (a - b) * (a + b + 1) = 2 * n := by
  obtain ⟨c, rfl⟩ : ∃ c, a = b + c := ⟨a - b, by omega⟩
  simp only [Nat.add_sub_cancel_left]
  have : (b + c) * (b + c + 1) = b * (b + 1) + c * (b + c + b + 1) := by ring
  rw [this] at h
  have : c * (b + c + b + 1) = 2 * n := by omega
  rw [← this]

theorem A135571_card_reps0 (n : ℕ) (hn : 1 ≤ n) :
    (A135571_reps0 n).card = (n.divisors.filter Odd).card := by
  apply Finset.card_bij (fun p _ => A135571_odd p)
  · rintro ⟨a, b⟩ hp
    simp only [A135571_reps0, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨-, hab, h⟩ := hp
    have hprod := A135571_prod a b n hab h
    simp only [Finset.mem_filter, Nat.mem_divisors, A135571_odd]
    split_ifs with hodd
    · refine ⟨⟨?_, by omega⟩, Nat.odd_iff.2 hodd⟩
      have : (a - b) ∣ 2 * n := ⟨_, hprod.symm⟩
      exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.2 (Nat.odd_iff.2 hodd)) this)
    · have hodd' : (a + b + 1) % 2 = 1 := by omega
      refine ⟨⟨?_, by omega⟩, Nat.odd_iff.2 hodd'⟩
      have : (a + b + 1) ∣ 2 * n := ⟨a - b, by rw [← hprod]; ring⟩
      exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.2 (Nat.odd_iff.2 hodd')) this)
  · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' he
    simp only [A135571_reps0, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp hp'
    obtain ⟨-, hab, h⟩ := hp
    obtain ⟨-, hab', h'⟩ := hp'
    have p1 := A135571_prod a b n hab h
    have p2 := A135571_prod a' b' n hab' h'
    simp only [A135571_odd] at he
    /- x = a - b < y = a + b + 1, x y = 2n; the odd one determines both -/
    have key : a - b = a' - b' ∧ a + b + 1 = a' + b' + 1 := by
      split_ifs at he with h1 h2 h2
      · refine ⟨he, ?_⟩
        have hx : 0 < a - b := by omega
        exact Nat.eq_of_mul_eq_mul_left hx (by rw [p1, he, p2])
      · exfalso
        /- a - b = a' + b' + 1 and then a + b + 1 = a' - b' -/
        have hx : 0 < a - b := by omega
        have : a + b + 1 = a' - b' := by
          apply Nat.eq_of_mul_eq_mul_left hx
          rw [p1, he, ← p2]; ring
        omega
      · exfalso
        have hx : 0 < a + b + 1 := by omega
        have : a - b = a' + b' + 1 := by
          apply Nat.eq_of_mul_eq_mul_left hx
          rw [mul_comm, p1, he, ← p2]
        omega
      · refine ⟨?_, he⟩
        have hy : 0 < a + b + 1 := by omega
        apply Nat.eq_of_mul_eq_mul_left hy
        rw [mul_comm, p1, he, ← p2, mul_comm]
    obtain ⟨k1, k2⟩ := key
    have : a = a' := by omega
    have : b = b' := by omega
    simp_all
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdn, -⟩, hdodd⟩ := hd
    obtain ⟨e', he'⟩ := hdn
    /- 2n = d · e with e = 2e' even -/
    have hd0 : 0 < d := hdodd.pos
    have he0 : 0 < e' := by
      rcases Nat.eq_zero_or_pos e' with h0 | h0
      · subst h0; omega
      · exact h0
    obtain ⟨r, hr⟩ := hdodd
    set e := 2 * e'
    /- u = min, v = max -/
    rcases lt_or_gt_of_ne (show d ≠ e by omega) with hlt | hgt
    · refine ⟨((e - d - 1) / 2 + d, (e - d - 1) / 2), ?_, ?_⟩
      · simp only [A135571_reps0, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        have hb2 : 2 * ((e - d - 1) / 2) = e - d - 1 := by omega
        set b := (e - d - 1) / 2
        have hv : e = 2 * b + d + 1 := by omega
        have hrel : (b + d) * (b + d + 1) = b * (b + 1) + 2 * n := by
          have : 2 * n = d * e := by rw [he']; ring
          rw [this, hv]; ring
        refine ⟨⟨?_, ?_⟩, by omega, hrel⟩
        · have := A135571_bound n (b + d) b (by omega) hrel; omega
        · have := A135571_bound n (b + d) b (by omega) hrel; omega
      · simp only [A135571_odd]
        split_ifs <;> omega
    · refine ⟨((d - e - 1) / 2 + e, (d - e - 1) / 2), ?_, ?_⟩
      · simp only [A135571_reps0, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        have hb2 : 2 * ((d - e - 1) / 2) = d - e - 1 := by omega
        set b := (d - e - 1) / 2
        have hv : d = 2 * b + e + 1 := by omega
        have hrel : (b + e) * (b + e + 1) = b * (b + 1) + 2 * n := by
          have : 2 * n = e * d := by rw [he']; ring
          rw [this, hv]; ring
        refine ⟨⟨?_, ?_⟩, by omega, hrel⟩
        · have := A135571_bound n (b + e) b (by omega) hrel; omega
        · have := A135571_bound n (b + e) b (by omega) hrel; omega
      · simp only [A135571_odd]
        split_ifs <;> omega

/-! ### b = 0 -/

open scoped Classical in
theorem A135571_card_reps0_eq (n : ℕ) (hn : 1 ≤ n) :
    (A135571_reps0 n).card = (A135571_reps n).card + if A135571_tri n then 1 else 0 := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := A135571_reps0 n) (fun p => 1 ≤ p.2)
  rw [← hsplit, A135571_reps]
  congr 1
  split_ifs with ht
  · obtain ⟨k, hk⟩ := ht
    rw [Finset.card_eq_one]
    refine ⟨(k, 0), ?_⟩
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, A135571_reps0, Finset.mem_product, Finset.mem_range,
      Finset.mem_singleton, Prod.mk.injEq, not_le, Nat.lt_one_iff]
    constructor
    · rintro ⟨⟨-, -, h⟩, rfl⟩
      refine ⟨?_, rfl⟩
      simp only [zero_mul, zero_add] at h
      rcases lt_trichotomy a k with h1 | h1 | h1
      · have : a * (a + 1) < k * (k + 1) := Nat.mul_lt_mul'' h1 (by omega)
        omega
      · exact h1
      · have : k * (k + 1) < a * (a + 1) := Nat.mul_lt_mul'' h1 (by omega)
        omega
    · rintro ⟨rfl, rfl⟩
      have hk0 : 0 < a := by
        rcases Nat.eq_zero_or_pos a with h | h
        · subst h; omega
        · exact h
      refine ⟨⟨⟨?_, by omega⟩, hk0, by simp only [zero_mul, zero_add]; omega⟩, rfl⟩
      have := A135571_bound n a 0 hk0 (by simp only [zero_mul, zero_add]; omega)
      omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨a, b⟩ hp hb
    simp only [not_le, Nat.lt_one_iff] at hb
    subst hb
    simp only [A135571_reps0, Finset.mem_filter] at hp
    exact ht ⟨a, by simp only [zero_mul, zero_add] at hp; omega⟩

/-! ### Parity of the number of odd divisors -/

theorem A135571_odd_prod {s : Finset ℕ} (f : ℕ → ℕ) :
    Odd (∏ x ∈ s, f x) ↔ ∀ x ∈ s, Odd (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Nat.odd_mul, ih, Finset.forall_mem_insert]

theorem A135571_odd_card_divisors (m : ℕ) (hm : m ≠ 0) :
    Odd m.divisors.card ↔ IsSquare m := by
  rw [Nat.card_divisors hm, A135571_odd_prod, Nat.isSquare_iff_even_factorization]
  constructor
  · intro h p hp
    by_cases hpm : p ∈ m.primeFactors
    · have := h p hpm
      rw [Nat.odd_add_one] at this
      exact Nat.not_odd_iff_even.1 this
    · rw [Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])]
      exact ⟨0, rfl⟩
  · intro h p hp
    rw [Nat.odd_add_one]
    exact Nat.not_odd_iff_even.2 (h p (Nat.prime_of_mem_primeFactors hp))

theorem A135571_odd_divisors (n : ℕ) (hn : n ≠ 0) :
    Odd (n.divisors.filter Odd).card ↔ (IsSquare n ∨ ∃ m, n = 2 * m ^ 2) := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  /- odd divisors of 2^k m = divisors of m -/
  have hdiv : (2 ^ k * m).divisors.filter Odd = m.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, -⟩, hdo⟩
      exact ⟨(Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hdo)).dvd_of_dvd_mul_left hd, hm0⟩
    · rintro ⟨hd, -⟩
      exact ⟨⟨Dvd.dvd.mul_left hd _, hn⟩, Odd.of_dvd_nat hm hd⟩
  rw [hdiv, A135571_odd_card_divisors m hm0]
  /- 2-adic valuations -/
  have hv : ∀ x : ℕ, x ≠ 0 → Even ((x ^ 2).factorization 2) := by
    intro x hx
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]; exact even_two_mul _
  have hm2 : m.factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    exact fun h => (by decide : ¬ Odd 2) (Odd.of_dvd_nat hm h)
  have hfac : (2 ^ k * m).factorization 2 = k := by
    rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply, hm2, Nat.factorization_pow,
      Finsupp.smul_apply, Nat.prime_two.factorization_self]; simp
  constructor
  · rintro ⟨r, rfl⟩
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · left; exact ⟨2 ^ j * r, by ring⟩
    · right; exact ⟨2 ^ j * r, by ring⟩
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · /- k even, so m = (x / 2^(k/2))^2 -/
      have hx0 : x ≠ 0 := by rintro rfl; simp at hx; omega
      have hk : Even k := by
        have := hv x hx0; rwa [sq, ← hx, hfac] at this
      obtain ⟨j, rfl⟩ := hk
      rw [Nat.isSquare_iff_even_factorization]
      intro p hp
      have h1 := (Nat.isSquare_iff_even_factorization.1 ⟨x, hx⟩) p hp
      rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply, Nat.factorization_pow,
        Finsupp.smul_apply] at h1
      by_cases hp2 : p = 2
      · subst hp2; rw [hm2]; exact ⟨0, rfl⟩
      · rw [Nat.factorization_eq_zero_of_not_dvd (fun h =>
          hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)), smul_zero, zero_add] at h1
        exact h1
    · have hx0 : x ≠ 0 := by rintro rfl; simp at hx; omega
      rw [Nat.isSquare_iff_even_factorization]
      intro p hp
      have h1 : (2 ^ k * m).factorization p = (2 * x ^ 2).factorization p := by rw [hx]
      rw [Nat.factorization_mul (by positivity) hm0, Nat.factorization_mul (by norm_num)
        (pow_ne_zero 2 hx0), Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_pow,
        Nat.factorization_pow, Finsupp.smul_apply, Finsupp.smul_apply] at h1
      by_cases hp2 : p = 2
      · subst hp2; rw [hm2]; exact ⟨0, rfl⟩
      · have hnd : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
        rw [Nat.factorization_eq_zero_of_not_dvd hnd, smul_zero, zero_add, zero_add] at h1
        rw [h1]; simp

/-! ### A twice-square is not triangular -/

theorem A135571_not_tri_twice_sq (m : ℕ) (hm : m ≠ 0) : ¬ A135571_tri (2 * m ^ 2) := by
  rintro ⟨k, hk⟩
  /- k(k+1) = (2m)^2 lies strictly between k^2 and (k+1)^2 -/
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk; exact absurd hk (by positivity)
    · exact h
  have e : (2 * m) ^ 2 = k * (k + 1) := by rw [← hk]; ring
  have h1 : k ^ 2 < (2 * m) ^ 2 := by rw [e]; nlinarith
  have h2 : (2 * m) ^ 2 < (k + 1) ^ 2 := by rw [e]; nlinarith
  have h1' := (Nat.pow_lt_pow_iff_left (by norm_num)).1 h1
  have h2' := (Nat.pow_lt_pow_iff_left (by norm_num)).1 h2
  omega

open scoped Classical in
theorem A135571_main (n : ℕ) (hn : 1 ≤ n) :
    Odd (A135571_reps n).card ↔
      (IsSquare n ∨ (∃ m, n = 2 * m ^ 2) ∨ A135571_tri n) ∧ ¬ (IsSquare n ∧ A135571_tri n) := by
  have h0 := A135571_card_reps0_eq n hn
  rw [A135571_card_reps0 n hn] at h0
  have hD := A135571_odd_divisors n (by omega)
  by_cases ht : A135571_tri n
  · simp only [ht, ↓reduceIte] at h0
    have hnot2 : ¬ ∃ m, n = 2 * m ^ 2 := by
      rintro ⟨m, rfl⟩
      exact A135571_not_tri_twice_sq m (by rintro rfl; simp at hn) ht
    have : Odd (A135571_reps n).card ↔ ¬ Odd (n.divisors.filter Odd).card := by
      rw [h0, Nat.odd_add_one, not_not]
    rw [this, hD]
    tauto
  · simp only [ht, ↓reduceIte, add_zero] at h0
    rw [← h0, hD]
    tauto
