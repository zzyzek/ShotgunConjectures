/-
OEIS A060275, original definition (Nomoto 2001): numbers n = a+b+c = x+y+z with
a*b*c = x*y*z (positive integers), p_k the k-th prime, i = p_a*p_b*p_c, j = p_x*p_y*p_z,
i != j. Old comment: "Conjecture: we always have gcd(i,j)=1." R. Israel (2015) replaced it by
"Any two such triples are disjoint", since a pair is fixed by its sum and product.

  * `A060275_pair`: a + b + c = a + y + z and a*b*c = a*y*z with a >= 1 force
    {b, c} = {y, z}.
  * `A060275_disjoint`: under the definition's hypotheses (i != j), a, b, c each differ
    from x, y, z.
  * `A060275_main`: gcd(i, j) = 1 (`Nat.Coprime`), with p_k = `Nat.nth Nat.Prime (k - 1)`.
Checked: all of the above, for all positive triples. Not checked: nothing beyond reading the
OEIS wording (ordering a <= b <= c is not needed).
-/
import Mathlib

/-- The k-th prime, 1-indexed (p_1 = 2). -/
noncomputable def A060275_p (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

theorem A060275_pair (a b c y z : ℕ) (ha : 1 ≤ a) (hs : a + b + c = a + y + z)
    (hp : a * b * c = a * y * z) : (b = y ∧ c = z) ∨ (b = z ∧ c = y) := by
  have hs' : b + c = y + z := by omega
  have hp' : b * c = y * z := by
    have : a * (b * c) = a * (y * z) := by rw [← mul_assoc, hp, mul_assoc]
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have key : ((b : ℤ) - y) * ((b : ℤ) - z) = 0 := by
    have e1 : (c : ℤ) = y + z - b := by omega
    have e2 : (b : ℤ) * c = y * z := by exact_mod_cast hp'
    rw [e1] at e2
    linear_combination -e2
  rcases mul_eq_zero.mp key with h | h
  · left; omega
  · right; omega

theorem A060275_first (a b c x y z : ℕ) (ha : 1 ≤ a)
    (hs : a + b + c = x + y + z) (hp : a * b * c = x * y * z)
    (hne : A060275_p a * A060275_p b * A060275_p c ≠ A060275_p x * A060275_p y * A060275_p z) :
    a ≠ x := by
  rintro rfl
  rcases A060275_pair a b c y z ha hs hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hne rfl
  · apply hne; ring

theorem A060275_disjoint (a b c x y z : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hs : a + b + c = x + y + z) (hp : a * b * c = x * y * z)
    (hne : A060275_p a * A060275_p b * A060275_p c ≠ A060275_p x * A060275_p y * A060275_p z) :
    a ≠ x ∧ a ≠ y ∧ a ≠ z ∧ b ≠ x ∧ b ≠ y ∧ b ≠ z ∧ c ≠ x ∧ c ≠ y ∧ c ≠ z := by
  set P := A060275_p
  -- Put the element of the first triple and the element of the second triple in front.
  have F : ∀ u v w u' v' w' : ℕ, 1 ≤ u → u + v + w = u' + v' + w' → u * v * w = u' * v' * w' →
      P u * P v * P w ≠ P u' * P v' * P w' → u ≠ u' := fun u v w u' v' w' h1 h2 h3 h4 =>
    A060275_first u v w u' v' w' h1 h2 h3 h4
  refine ⟨F a b c x y z ha hs hp hne,
    F a b c y x z ha (by omega) (by rw [hp]; ring) (by intro h; apply hne; rw [h]; ring),
    F a b c z x y ha (by omega) (by rw [hp]; ring) (by intro h; apply hne; rw [h]; ring),
    F b a c x y z hb (by omega) (by rw [← hp]; ring) (by intro h; apply hne; rw [← h]; ring),
    F b a c y x z hb (by omega) (by rw [show b * a * c = a * b * c by ring, hp]; ring)
      (by intro h; apply hne; linear_combination h),
    F b a c z x y hb (by omega) (by rw [show b * a * c = a * b * c by ring, hp]; ring)
      (by intro h; apply hne; linear_combination h),
    F c a b x y z hc (by omega) (by rw [show c * a * b = a * b * c by ring, hp])
      (by intro h; apply hne; linear_combination h),
    F c a b y x z hc (by omega) (by rw [show c * a * b = a * b * c by ring, hp]; ring)
      (by intro h; apply hne; linear_combination h),
    F c a b z x y hc (by omega) (by rw [show c * a * b = a * b * c by ring, hp]; ring)
      (by intro h; apply hne; linear_combination h)⟩

theorem A060275_p_coprime (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (h : u ≠ v) :
    Nat.Coprime (A060275_p u) (A060275_p v) := by
  unfold A060275_p
  rw [Nat.coprime_primes (Nat.prime_nth_prime _) (Nat.prime_nth_prime _)]
  intro e
  have := Nat.nth_injective Nat.infinite_setOfPred_prime e
  omega

theorem A060275_main (a b c x y z : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hs : a + b + c = x + y + z) (hp : a * b * c = x * y * z)
    (hne : A060275_p a * A060275_p b * A060275_p c ≠ A060275_p x * A060275_p y * A060275_p z) :
    Nat.Coprime (A060275_p a * A060275_p b * A060275_p c)
      (A060275_p x * A060275_p y * A060275_p z) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := A060275_disjoint a b c x y z ha hb hc hs hp hne
  have row : ∀ u, 1 ≤ u → u ≠ x → u ≠ y → u ≠ z →
      Nat.Coprime (A060275_p u) (A060275_p x * A060275_p y * A060275_p z) :=
    fun u hu e1 e2 e3 =>
      Nat.Coprime.mul_right (Nat.Coprime.mul_right (A060275_p_coprime u x hu hx e1)
        (A060275_p_coprime u y hu hy e2)) (A060275_p_coprime u z hu hz e3)
  exact Nat.coprime_mul_iff_left.mpr
    ⟨Nat.coprime_mul_iff_left.mpr ⟨row a ha h1 h2 h3, row b hb h4 h5 h6⟩, row c hc h7 h8 h9⟩
