/-
OEIS A134002: positive n such that n(n+5) = a(a+5) + b(b+5) is solvable in
positive integers.  Conjecture (Layman 2007): if n is not a term, then
n^2 + (n+5)^2 is prime.

Main theorem `A134002_iff`: for every n ≥ 1, the equation has a solution in
positive integers a, b iff M = n^2 + (n+5)^2 is not prime.  The conjecture
is the direction `A134002_conjecture` (no solution → M prime); the converse
(OEIS-A134003) is included.  This is the README result.

Proof.  A solution is the same as M = u^2 + v^2 with u = a+b+5, v = a-b
(a ≥ b), and conversely a representation M = u^2 + v^2 with u - v ≥ 7 gives
a = (u+v-5)/2, b = (u-v-5)/2.
* M prime: the representation of a prime is unique (`sq_add_sq_unique`), so
  only {n+5, n} occurs and b = 0.
* 5 ∣ n, n = 5(i+1): a = 3i+4, b = 4i+2.
* 5 ∤ n, M composite: gcd(n, n+5) = 1, so -1 is a square mod M
  (Mathlib `ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime`) and every
  divisor of M is a sum of two squares (`Nat.eq_sq_add_sq_of_isSquare_mod_neg_one`).
  Writing M = d·e with d, e ≥ 2, d = s^2+t^2, e = x^2+y^2, one of the two
  Brahmagupta products (sx ∓ ty)^2 + (sy ± tx)^2 differs from {n, n+5}
  (`second_rep`: otherwise d or e is a square c^2 with c ∣ gcd(n, n+5), or is
  twice a square, contradicting M odd).  The new representation has u - v odd
  and ∉ {1, 3, 5}, so u - v ≥ 7.

Not checked: nothing outside Lean.
-/
import Mathlib

/-- If x is a multiple of p and x^2 ≤ p^2 then x ∈ {-p, 0, p}. -/
lemma mult_small {p x : ℤ} (hp : 0 < p) (hd : p ∣ x) (hs : x ^ 2 ≤ p ^ 2) :
    x = -p ∨ x = 0 ∨ x = p := by
  obtain ⟨t, rfl⟩ := hd
  have ht : t ^ 2 ≤ 1 := by
    have : p ^ 2 * t ^ 2 ≤ p ^ 2 * 1 := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have h1 : -1 ≤ t := by nlinarith
  have h2 : t ≤ 1 := by nlinarith
  interval_cases t <;> simp

lemma sq_sum_zero {a b c d : ℤ} (h : (a - c) ^ 2 + (b - d) ^ 2 = 0) : a = c ∧ b = d := by
  have h3 : (a - c) ^ 2 = 0 := by linarith [sq_nonneg (a - c), sq_nonneg (b - d)]
  have h4 : (b - d) ^ 2 = 0 := by linarith [sq_nonneg (a - c), sq_nonneg (b - d)]
  exact ⟨sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3),
    sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)⟩

/-- Uniqueness of the two-squares representation of a prime. -/
lemma sq_add_sq_unique {p : ℕ} (hp : p.Prime) {a b c d : ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h1 : (p : ℤ) = a ^ 2 + b ^ 2) (h2 : (p : ℤ) = c ^ 2 + d ^ 2) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  -- No square is a prime, so all four entries are positive.
  have nsq : ∀ x : ℤ, 0 ≤ x → (p : ℤ) ≠ x ^ 2 := by
    intro x hx hpx
    have : (p : ℤ) = (x.toNat : ℤ) ^ 2 := by rw [Int.toNat_of_nonneg hx]; exact hpx
    have : p = x.toNat ^ 2 := by exact_mod_cast this
    exact Nat.Prime.not_prime_pow le_rfl (this ▸ hp)
  have ha' : 0 < a := lt_of_le_of_ne ha (by rintro rfl; exact nsq b hb (by rw [h1]; ring))
  have hb' : 0 < b := lt_of_le_of_ne hb (by rintro rfl; exact nsq a ha (by rw [h1]; ring))
  have hc' : 0 < c := lt_of_le_of_ne hc (by rintro rfl; exact nsq d hd (by rw [h2]; ring))
  have hd' : 0 < d := lt_of_le_of_ne hd (by rintro rfl; exact nsq c hc (by rw [h2]; ring))
  have key : (a * d - b * c) * (a * d + b * c) = (p : ℤ) * (a ^ 2 - c ^ 2) := by
    rw [h1] at *; nlinarith [h1, h2]
  have e1 : (a * d + b * c) ^ 2 + (a * c - b * d) ^ 2 = (p : ℤ) ^ 2 := by
    rw [sq (p : ℤ)]; nth_rewrite 1 [h1]; rw [h2]; ring
  have e2 : (a * d - b * c) ^ 2 + (a * c + b * d) ^ 2 = (p : ℤ) ^ 2 := by
    rw [sq (p : ℤ)]; nth_rewrite 1 [h1]; rw [h2]; ring
  have hdvd : (p : ℤ) ∣ (a * d - b * c) * (a * d + b * c) := ⟨_, key⟩
  rcases hpz.dvd_or_dvd hdvd with hdv | hdv
  · rcases mult_small hp0 hdv (by nlinarith) with h | h | h
    · have : (a * c + b * d) ^ 2 = 0 := by rw [h] at e2; linarith
      have : a * c + b * d = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp this
      nlinarith [mul_pos ha' hc', mul_pos hb' hd']
    · have hs : (a * c + b * d) ^ 2 = (p : ℤ) ^ 2 := by rw [h] at e2; linarith
      have hs' : a * c + b * d = p := by
        have := (sq_eq_sq₀ (by positivity) hp0.le).mp hs; exact this
      left
      have : (a - c) ^ 2 + (b - d) ^ 2 = 0 := by linear_combination (-1) * h1 - h2 - 2 * hs'
      exact sq_sum_zero this
    · have : (a * c + b * d) ^ 2 = 0 := by rw [h] at e2; linarith
      have : a * c + b * d = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp this
      nlinarith [mul_pos ha' hc', mul_pos hb' hd']
  · rcases mult_small hp0 hdv (by nlinarith) with h | h | h
    · nlinarith [mul_pos ha' hd', mul_pos hb' hc']
    · nlinarith [mul_pos ha' hd', mul_pos hb' hc']
    · right
      have : (a - d) ^ 2 + (b - c) ^ 2 = 0 := by linear_combination (-1) * h1 - h2 - 2 * h
      exact sq_sum_zero this

theorem A134003_positive (n a b : ℕ) (hM : (n ^ 2 + (n + 5) ^ 2).Prime)
    (ha : 0 < a) (hb : 0 < b) : n * (n + 5) ≠ a * (a + 5) + b * (b + 5) := by
  intro heq
  -- Symmetric in a, b; reduce to b ≤ a.
  wlog hab : b ≤ a generalizing a b
  · exact this b a hb ha (by rw [heq]; ring) (by omega)
  have hz : ((n ^ 2 + (n + 5) ^ 2 : ℕ) : ℤ) = ((a : ℤ) + b + 5) ^ 2 + ((a : ℤ) - b) ^ 2 := by
    have : ((n * (n + 5) : ℕ) : ℤ) = ((a * (a + 5) + b * (b + 5) : ℕ) : ℤ) := by rw [heq]
    push_cast at this ⊢; nlinarith [this]
  have hz2 : ((n ^ 2 + (n + 5) ^ 2 : ℕ) : ℤ) = ((n : ℤ) + 5) ^ 2 + (n : ℤ) ^ 2 := by
    push_cast; ring
  rcases sq_add_sq_unique hM (by positivity) (by omega) (by positivity) (by positivity) hz hz2
    with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- A common factor of P and Q, when {P^2, Q^2} = {n^2, m^2} and n, m are
coprime, is a unit. -/
lemma common_factor {c P Q n m : ℤ} (hcP : c ∣ P) (hcQ : c ∣ Q)
    (h : (P ^ 2 = n ^ 2 ∧ Q ^ 2 = m ^ 2) ∨ (P ^ 2 = m ^ 2 ∧ Q ^ 2 = n ^ 2))
    (hcop : IsCoprime n m) : c ^ 2 = 1 := by
  have dv : ∀ {X Y : ℤ}, c ∣ X → X ^ 2 = Y ^ 2 → c ∣ Y := by
    intro X Y hX hXY
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hXY with h | h
    · rw [← h]; exact hX
    · rw [show Y = -X by rw [h]; ring]; exact (dvd_neg).2 hX
  have hu : IsUnit c := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hcop.isUnit_of_dvd' (dv hcP h1) (dv hcQ h2)
    · exact hcop.isUnit_of_dvd' (dv hcQ h2) (dv hcP h1)
  rcases Int.isUnit_iff.1 hu with rfl | rfl <;> norm_num

lemma odd_ne_two_mul {d s : ℤ} (hd : Odd d) (h : d = 2 * s ^ 2) : False := by
  have := Int.odd_iff.mp hd
  rw [h, Int.mul_emod_right] at this
  exact absurd this (by norm_num)

/-- If d·e = n^2 + m^2 with d, e ≥ 2 odd sums of two squares and gcd(n, m) = 1,
there is a representation n^2 + m^2 = P^2 + Q^2 with P^2 ∉ {n^2, m^2}. -/
lemma second_rep {n m s t x y : ℤ} (hcop : IsCoprime n m)
    (hd : 2 ≤ s ^ 2 + t ^ 2) (he : 2 ≤ x ^ 2 + y ^ 2)
    (hdo : Odd (s ^ 2 + t ^ 2)) (heo : Odd (x ^ 2 + y ^ 2))
    (hM : (s ^ 2 + t ^ 2) * (x ^ 2 + y ^ 2) = n ^ 2 + m ^ 2) :
    ∃ P Q : ℤ, n ^ 2 + m ^ 2 = P ^ 2 + Q ^ 2 ∧ P ^ 2 ≠ n ^ 2 ∧ P ^ 2 ≠ m ^ 2 := by
  by_contra H
  push Not at H
  have hPQ : n ^ 2 + m ^ 2 = (s * x - t * y) ^ 2 + (s * y + t * x) ^ 2 := by rw [← hM]; ring
  have hRT : n ^ 2 + m ^ 2 = (s * x + t * y) ^ 2 + (s * y - t * x) ^ 2 := by rw [← hM]; ring
  have cls : ∀ P Q : ℤ, n ^ 2 + m ^ 2 = P ^ 2 + Q ^ 2 →
      (P ^ 2 = n ^ 2 ∧ Q ^ 2 = m ^ 2) ∨ (P ^ 2 = m ^ 2 ∧ Q ^ 2 = n ^ 2) := by
    intro P Q hpq
    by_cases h1 : P ^ 2 = n ^ 2
    · left; exact ⟨h1, by linarith⟩
    · right; have h2 := H P Q hpq h1; exact ⟨h2, by linarith⟩
  have cP := cls _ _ hPQ
  have cR := cls _ _ hRT
  by_cases hPR : (s * x - t * y) ^ 2 = (s * x + t * y) ^ 2
  · have h0 : s * x * (t * y) = 0 := by nlinarith
    rcases mul_eq_zero.1 h0 with h0 | h0 <;> rcases mul_eq_zero.1 h0 with h0 | h0
    · subst h0
      have := common_factor (c := t) ⟨-y, by ring⟩ ⟨x, by ring⟩ cP hcop
      nlinarith
    · subst h0
      have := common_factor (c := y) ⟨-t, by ring⟩ ⟨s, by ring⟩ cP hcop
      nlinarith
    · subst h0
      have := common_factor (c := s) ⟨x, by ring⟩ ⟨y, by ring⟩ cP hcop
      nlinarith
    · subst h0
      have := common_factor (c := x) ⟨s, by ring⟩ ⟨t, by ring⟩ cP hcop
      nlinarith
  · -- P^2 ≠ R^2, so T^2 = P^2.
    have hT : (s * y - t * x) ^ 2 = (s * x - t * y) ^ 2 := by
      rcases cP with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases cR with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact absurd (h1.trans h3.symm) hPR
      · linarith
      · linarith
      · exact absurd (h1.trans h3.symm) hPR
    have h0 : ((s + t) * (x - y)) * ((s - t) * (x + y)) = 0 := by linear_combination -hT
    rcases mul_eq_zero.1 h0 with h0 | h0 <;> rcases mul_eq_zero.1 h0 with h0 | h0
    · exact odd_ne_two_mul hdo (s := s) (by
        have : t = -s := by linarith
        rw [this]; ring)
    · exact odd_ne_two_mul heo (s := x) (by
        have : y = x := by linarith
        rw [this]; ring)
    · exact odd_ne_two_mul hdo (s := s) (by
        have : t = s := by linarith
        rw [this]; ring)
    · exact odd_ne_two_mul heo (s := x) (by
        have : y = -x := by linarith
        rw [this]; ring)

/-- From a representation n^2 + (n+5)^2 = u^2 + v^2 avoiding {n, n+5},
build a positive solution. -/
lemma finish (n u v : ℕ) (hn : 1 ≤ n) (hM : n ^ 2 + (n + 5) ^ 2 = u ^ 2 + v ^ 2)
    (hu1 : u ≠ n) (hu2 : u ≠ n + 5) (hv1 : v ≠ n) (hv2 : v ≠ n + 5) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n * (n + 5) = a * (a + 5) + b * (b + 5) := by
  wlog hvu : v ≤ u generalizing u v
  · exact this v u (by rw [hM]; ring) hv1 hv2 hu1 hu2 (by omega)
  obtain ⟨δ, rfl⟩ : ∃ δ, u = v + δ := ⟨u - v, by omega⟩
  have hM' : 2 * n ^ 2 + 10 * n + 25 = 2 * v ^ 2 + 2 * v * δ + δ ^ 2 := by
    have := hM; ring_nf at this ⊢; linarith
  -- δ is odd.
  have hodd : δ % 2 = 1 := by
    rcases Nat.even_or_odd δ with ⟨k, hk⟩ | ⟨k, hk⟩
    · exfalso
      subst hk
      have : 2 * n ^ 2 + 10 * n + 25 = 2 * (v ^ 2 + 2 * v * k + 2 * k ^ 2) := by
        rw [hM']; ring
      omega
    · omega
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    rcases Nat.lt_or_ge v (n + 3) with h | h
    · have : v ≤ n + 2 := by omega
      nlinarith
    · nlinarith
  have hδ3 : δ ≠ 3 := by
    rintro rfl
    rcases Nat.lt_or_ge v (n + 2) with h | h
    · have : v ≤ n + 1 := by omega
      nlinarith
    · nlinarith
  have hδ5 : δ ≠ 5 := by
    rintro rfl
    rcases Nat.lt_or_ge v n with h | h
    · have : v + 1 ≤ n := by omega
      nlinarith
    · have : n + 1 ≤ v := by omega
      nlinarith
  obtain ⟨b, rfl⟩ : ∃ b, δ = 2 * b + 5 := ⟨(δ - 5) / 2, by omega⟩
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h; simp at hδ5
    · exact h
  refine ⟨v + b, b, by omega, hb, ?_⟩
  have h2 : 2 * (n * (n + 5)) = 2 * ((v + b) * (v + b + 5) + b * (b + 5)) := by
    zify at hM' ⊢; linear_combination hM'
  omega

lemma not_prime_of_sol (n a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : n * (n + 5) = a * (a + 5) + b * (b + 5)) : ¬ (n ^ 2 + (n + 5) ^ 2).Prime :=
  fun hM => A134003_positive n a b hM ha hb h

theorem A134002_iff (n : ℕ) (hn : 1 ≤ n) :
    (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n * (n + 5) = a * (a + 5) + b * (b + 5)) ↔
      ¬ (n ^ 2 + (n + 5) ^ 2).Prime := by
  constructor
  · rintro ⟨a, b, ha, hb, h⟩; exact not_prime_of_sol n a b ha hb h
  · intro hnp
    by_cases h5 : 5 ∣ n
    · obtain ⟨j, rfl⟩ := h5
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact ⟨3 * i + 4, 4 * i + 2, by omega, by omega, by ring⟩
    · set M := n ^ 2 + (n + 5) ^ 2 with hMdef
      have hcopN : Nat.Coprime n (n + 5) := by
        rw [Nat.coprime_self_add_right]
        exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5)
      have hsq : IsSquare (-1 : ZMod M) :=
        ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime rfl hcopN
      have hM2 : 2 ≤ M := by nlinarith
      have hModd : M % 2 = 1 := by
        have : M = 2 * (n ^ 2 + 5 * n + 12) + 1 := by rw [hMdef]; ring
        omega
      set d := M.minFac
      have hdM : d ∣ M := Nat.minFac_dvd M
      have hdlt : d < M := (Nat.not_prime_iff_minFac_lt hM2).1 hnp
      have hd2 : 2 ≤ d := (Nat.minFac_prime (by omega)).two_le
      obtain ⟨e, he⟩ := hdM
      have he2 : 2 ≤ e := by
        rcases Nat.lt_or_ge e 2 with h | h
        · interval_cases e <;> omega
        · exact h
      obtain ⟨s, t, hst⟩ := Nat.eq_sq_add_sq_of_isSquare_mod_neg_one
        (ZMod.isSquare_neg_one_of_dvd ⟨e, he⟩ hsq)
      obtain ⟨x, y, hxy⟩ := Nat.eq_sq_add_sq_of_isSquare_mod_neg_one
        (ZMod.isSquare_neg_one_of_dvd (Dvd.intro_left d he.symm) hsq)
      have hdo : d % 2 = 1 := by
        rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
        · exfalso; rw [he, hk] at hModd; ring_nf at hModd; omega
        · omega
      have heo : e % 2 = 1 := by
        rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
        · exfalso; rw [he, hk] at hModd; ring_nf at hModd; omega
        · omega
      have hcopZ : IsCoprime (n : ℤ) ((n : ℤ) + 5) := by
        have := Nat.isCoprime_iff_coprime.mpr hcopN; push_cast at this; exact this
      obtain ⟨P, Q, hPQ, hPn, hPm⟩ := second_rep (n := (n : ℤ)) (m := (n : ℤ) + 5)
        (s := s) (t := t) (x := x) (y := y) hcopZ
        (by have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd2
            rw [hst] at this; push_cast at this; exact this)
        (by have : (2 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he2
            rw [hxy] at this; push_cast at this; exact this)
        (by rw [Int.odd_iff]; have : ((d : ℕ) : ℤ) % 2 = 1 := by exact_mod_cast hdo
            rw [hst] at this; push_cast at this; exact this)
        (by rw [Int.odd_iff]; have : ((e : ℕ) : ℤ) % 2 = 1 := by exact_mod_cast heo
            rw [hxy] at this; push_cast at this; exact this)
        (by have : ((M : ℕ) : ℤ) = (d : ℤ) * e := by exact_mod_cast he
            rw [hMdef, hst, hxy] at this; push_cast at this; rw [← this])
      have hu : ((P.natAbs : ℕ) : ℤ) ^ 2 = P ^ 2 := Int.natAbs_sq P
      have hv : ((Q.natAbs : ℕ) : ℤ) ^ 2 = Q ^ 2 := Int.natAbs_sq Q
      have hMuv : n ^ 2 + (n + 5) ^ 2 = P.natAbs ^ 2 + Q.natAbs ^ 2 := by
        have : ((n ^ 2 + (n + 5) ^ 2 : ℕ) : ℤ) = ((P.natAbs ^ 2 + Q.natAbs ^ 2 : ℕ) : ℤ) := by
          push_cast; rw [sq_abs, sq_abs]; exact hPQ
        exact_mod_cast this
      apply finish n P.natAbs Q.natAbs hn hMuv
      · intro h; apply hPn; rw [← hu, h]
      · intro h; apply hPm; rw [← hu, h]; push_cast; ring
      · intro h
        apply hPm
        have : (Q.natAbs : ℤ) = n := by exact_mod_cast h
        rw [← hv, this] at hPQ
        linarith
      · intro h
        apply hPn
        have : (Q.natAbs : ℤ) = n + 5 := by exact_mod_cast h
        rw [← hv, this] at hPQ
        linarith

theorem A134002_conjecture (n : ℕ) (hn : 1 ≤ n)
    (h : ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n * (n + 5) = a * (a + 5) + b * (b + 5)) :
    (n ^ 2 + (n + 5) ^ 2).Prime := by
  by_contra hp
  exact h ((A134002_iff n hn).2 hp)
