import Mathlib

/-!
# OEIS A084189 (and A084352): no palindromic semiprime has both prime factors with all digits ≥ 4

A084189(n): minimum digit of the two prime factors of A046376(n), where A046376 lists the palindromes
`p * q` with `p`, `q` palindromic primes. Conjecture: a(n) ≤ 3 for all n.

Digit lists are Mathlib's `Nat.digits 10` (least significant digit first); a palindrome is a number whose
digit list equals its reverse.

Checked here:
* `prod_length` : if every digit of `p > 0` and of `q > 0` is ≥ 4, then `p * q` has exactly
  `len p + len q` digits (no loss of a leading digit, since the leading digits multiply to ≥ 16).
* `odd_length` : a palindromic prime all of whose digits are ≥ 4 has an odd number of digits
  (an even-length palindrome is divisible by 11, and 11 has digit 1).
* `A084189_main` : if `p`, `q` are palindromic primes all of whose digits are ≥ 4, then `p * q` is not a
  palindrome. Hence the minimum digit of the factors of every term of A046376 is ≤ 3.
* `A084352_main` : if `p`, `q` are primes with the same number of digits, all digits ≥ 4, then `p * q` is not
  a palindrome (A084352, palindromic brilliant numbers).
* `A084189_sharp`, `A084352_sharp` : the same with "all digits ≥ 3", except `3 * 3 = 9`. So a(n) = 3 only for
  the term 9 (n = 3 in both entries) and a(n) ≤ 2 for every other n.
Not checked: agreement of these statements with the OEIS data lists (only the definitions are read).
-/

namespace A084189

open Nat

def IsPal (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- A digit list with every digit ≥ 4 has value at least `4 (10^len - 1) / 9`. -/
theorem low_bound (l : List ℕ) (h : ∀ x ∈ l, 4 ≤ x) :
    4 * 10 ^ l.length ≤ 9 * Nat.ofDigits 10 l + 4 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    rw [Nat.ofDigits_cons, List.length_cons, pow_succ]
    nlinarith

theorem digits_low (p : ℕ) (h : ∀ x ∈ Nat.digits 10 p, 4 ≤ x) :
    4 * 10 ^ (Nat.digits 10 p).length ≤ 9 * p + 4 := by
  have := low_bound (Nat.digits 10 p) h
  rwa [Nat.ofDigits_digits] at this

/-- The product has exactly `len p + len q` digits. -/
theorem prod_length (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hdp : ∀ x ∈ Nat.digits 10 p, 4 ≤ x) (hdq : ∀ x ∈ Nat.digits 10 q, 4 ≤ x) :
    (Nat.digits 10 (p * q)).length = (Nat.digits 10 p).length + (Nat.digits 10 q).length := by
  set a := (Nat.digits 10 p).length
  set b := (Nat.digits 10 q).length
  have hA : 10 ≤ 10 ^ a := by
    have : 1 ≤ a := List.length_pos_iff.2 (Nat.digits_ne_nil_iff_ne_zero.2 (by omega))
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ a := Nat.pow_le_pow_right (by norm_num) this
  have hB : 10 ≤ 10 ^ b := by
    have : 1 ≤ b := List.length_pos_iff.2 (Nat.digits_ne_nil_iff_ne_zero.2 (by omega))
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ b := Nat.pow_le_pow_right (by norm_num) this
  have lp := digits_low p hdp
  have lq := digits_low q hdq
  have up : p < 10 ^ a := Nat.lt_base_pow_length_digits (by norm_num)
  have uq : q < 10 ^ b := Nat.lt_base_pow_length_digits (by norm_num)
  have hupper : p * q < 10 ^ (a + b) := by
    rw [pow_add]; exact Nat.mul_lt_mul'' up uq
  have hlower : 10 ^ (a + b) ≤ 10 * (p * q) := by
    rw [pow_add]
    set A := 10 ^ a
    set B := 10 ^ b
    nlinarith
  apply le_antisymm
  · exact (Nat.digits_length_le_iff (by norm_num) _).2 hupper
  · by_contra hlt
    replace hlt := Nat.lt_of_not_le hlt
    have h1 := (Nat.digits_length_le_iff (by norm_num) (p * q)).1 (Nat.le_sub_one_of_lt hlt)
    have h2 : 10 * 10 ^ (a + b - 1) = 10 ^ (a + b) := by
      rw [← _root_.pow_succ']; congr 1; omega
    omega

/-- A prime all of whose digits are ≥ 4 is not divisible by 11. -/
theorem not_eleven (p : ℕ) (hp : p.Prime) (hd : ∀ x ∈ Nat.digits 10 p, 4 ≤ x) : ¬ 11 ∣ p := by
  intro h
  have : p = 11 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 h).symm
  subst this
  have := hd 1 (by norm_num)
  omega

theorem pal_of_IsPal {n : ℕ} (h : IsPal n) : (Nat.digits 10 n).Palindrome :=
  List.Palindrome.of_reverse_eq h

/-- A palindromic prime with all digits ≥ 4 has odd length. -/
theorem odd_length (p : ℕ) (hp : p.Prime) (hpal : IsPal p) (hd : ∀ x ∈ Nat.digits 10 p, 4 ≤ x) :
    ¬ Even (Nat.digits 10 p).length := fun he =>
  not_eleven p hp hd (Nat.eleven_dvd_of_palindrome (pal_of_IsPal hpal) he)

/-- Core: if the factors' lengths add to an even number, the product is not a palindrome. -/
theorem not_pal_of_even (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hdp : ∀ x ∈ Nat.digits 10 p, 4 ≤ x) (hdq : ∀ x ∈ Nat.digits 10 q, 4 ≤ x)
    (he : Even ((Nat.digits 10 p).length + (Nat.digits 10 q).length)) : ¬ IsPal (p * q) := by
  intro hpal
  rw [← prod_length p q hp.pos hq.pos hdp hdq] at he
  have h11 := Nat.eleven_dvd_of_palindrome (pal_of_IsPal hpal) he
  rcases (Nat.Prime.dvd_mul (by norm_num)).1 h11 with h | h
  · exact not_eleven p hp hdp h
  · exact not_eleven q hq hdq h

theorem A084189_main (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpp : IsPal p) (hqp : IsPal q)
    (hdp : ∀ x ∈ Nat.digits 10 p, 4 ≤ x) (hdq : ∀ x ∈ Nat.digits 10 q, 4 ≤ x) :
    ¬ IsPal (p * q) := by
  apply not_pal_of_even p q hp hq hdp hdq
  have h1 := odd_length p hp hpp hdp
  have h2 := odd_length q hq hqp hdq
  rw [Nat.not_even_iff_odd] at h1 h2
  exact Odd.add_odd h1 h2

theorem A084352_main (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hlen : (Nat.digits 10 p).length = (Nat.digits 10 q).length)
    (hdp : ∀ x ∈ Nat.digits 10 p, 4 ≤ x) (hdq : ∀ x ∈ Nat.digits 10 q, 4 ≤ x) :
    ¬ IsPal (p * q) := by
  apply not_pal_of_even p q hp hq hdp hdq
  rw [hlen]
  exact ⟨_, rfl⟩

/-! ## Sharper form: digits ≥ 3 -/

/-- A digit list with every digit ≥ 3 has value at least `(10^len - 1) / 3`. -/
theorem low_bound3 (l : List ℕ) (h : ∀ x ∈ l, 3 ≤ x) :
    10 ^ l.length ≤ 3 * Nat.ofDigits 10 l + 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    rw [Nat.ofDigits_cons, List.length_cons, pow_succ]
    nlinarith

theorem digits_low3 (p : ℕ) (h : ∀ x ∈ Nat.digits 10 p, 3 ≤ x) :
    10 ^ (Nat.digits 10 p).length ≤ 3 * p + 1 := by
  have := low_bound3 (Nat.digits 10 p) h
  rwa [Nat.ofDigits_digits] at this

/-- `3 q + 1 = 10^b` forces `3 ∣ q` (as `9 ∣ 10^b - 1`), so `q = 3` for a prime `q`. -/
theorem three_q (q b : ℕ) (hq : q.Prime) (h : 3 * q + 1 = 10 ^ b) : q = 3 := by
  have h9 : 10 ^ b % 9 = 1 := by
    rw [Nat.pow_mod]; norm_num
  have : 3 ∣ q := by omega
  exact ((Nat.prime_dvd_prime_iff_eq (by norm_num) hq).1 this).symm

theorem prod_length3 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hdp : ∀ x ∈ Nat.digits 10 p, 3 ≤ x) (hdq : ∀ x ∈ Nat.digits 10 q, 3 ≤ x)
    (h33 : ¬ (p = 3 ∧ q = 3)) :
    (Nat.digits 10 (p * q)).length = (Nat.digits 10 p).length + (Nat.digits 10 q).length := by
  set a := (Nat.digits 10 p).length
  set b := (Nat.digits 10 q).length
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have ha1 : 1 ≤ a := List.length_pos_iff.2 (Nat.digits_ne_nil_iff_ne_zero.2 (by omega))
  have hb1 : 1 ≤ b := List.length_pos_iff.2 (Nat.digits_ne_nil_iff_ne_zero.2 (by omega))
  have lp := digits_low3 p hdp
  have lq := digits_low3 q hdq
  have up : p < 10 ^ a := Nat.lt_base_pow_length_digits (by norm_num)
  have uq : q < 10 ^ b := Nat.lt_base_pow_length_digits (by norm_num)
  have hA : 10 ≤ 10 ^ a := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ a := Nat.pow_le_pow_right (by norm_num) ha1
  have hB : 10 ≤ 10 ^ b := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ b := Nat.pow_le_pow_right (by norm_num) hb1
  have hupper : p * q < 10 ^ (a + b) := by
    rw [pow_add]; exact Nat.mul_lt_mul'' up uq
  have hlower : 10 ^ (a + b) ≤ 10 * (p * q) := by
    rw [pow_add]
    set A := 10 ^ a
    set B := 10 ^ b
    rcases Nat.lt_or_ge a 2 with ha | ha
    · -- `p` has one digit, `p ≥ 3`, `A = 10`.
      have hA10 : A = 10 := by
        show 10 ^ a = 10
        rw [show a = 1 by omega]; norm_num
      rw [hA10]
      have hp3 : 3 ≤ p := by
        have := hdp (p % 10) (by rw [Nat.digits_def' (by norm_num) (by omega)]; simp)
        rw [hA10] at up
        rwa [Nat.mod_eq_of_lt up] at this
      rcases Nat.lt_or_ge p 4 with hp4 | hp4
      · have : p = 3 := by omega
        subst this
        have hq3 : q ≠ 3 := fun h => h33 ⟨rfl, h⟩
        have : 3 * q + 1 ≠ B := fun h => hq3 (three_q q b hq h)
        omega
      · nlinarith
    · rcases Nat.lt_or_ge b 2 with hb | hb
      · have hB10 : B = 10 := by
          show 10 ^ b = 10
          rw [show b = 1 by omega]; norm_num
        rw [hB10]
        have hq3 : 3 ≤ q := by
          have := hdq (q % 10) (by rw [Nat.digits_def' (by norm_num) (by omega)]; simp)
          rw [hB10] at uq
          rwa [Nat.mod_eq_of_lt uq] at this
        rcases Nat.lt_or_ge q 4 with hq4 | hq4
        · have : q = 3 := by omega
          subst this
          have hp3 : p ≠ 3 := fun h => h33 ⟨h, rfl⟩
          have : 3 * p + 1 ≠ A := fun h => hp3 (three_q p a hp h)
          omega
        · nlinarith
      · have hA100 : 100 ≤ A := by
          calc 100 = 10 ^ 2 := by norm_num
            _ ≤ 10 ^ a := Nat.pow_le_pow_right (by norm_num) ha
        have hB100 : 100 ≤ B := by
          calc 100 = 10 ^ 2 := by norm_num
            _ ≤ 10 ^ b := Nat.pow_le_pow_right (by norm_num) hb
        nlinarith
  apply le_antisymm
  · exact (Nat.digits_length_le_iff (by norm_num) _).2 hupper
  · by_contra hlt
    replace hlt := Nat.lt_of_not_le hlt
    have h1 := (Nat.digits_length_le_iff (by norm_num) (p * q)).1 (Nat.le_sub_one_of_lt hlt)
    have h2 : 10 * 10 ^ (a + b - 1) = 10 ^ (a + b) := by
      rw [← _root_.pow_succ']; congr 1; omega
    omega

theorem not_eleven3 (p : ℕ) (hp : p.Prime) (hd : ∀ x ∈ Nat.digits 10 p, 3 ≤ x) : ¬ 11 ∣ p := by
  intro h
  have : p = 11 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 h).symm
  subst this
  have := hd 1 (by norm_num)
  omega

theorem not_pal_of_even3 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hdp : ∀ x ∈ Nat.digits 10 p, 3 ≤ x) (hdq : ∀ x ∈ Nat.digits 10 q, 3 ≤ x)
    (h33 : ¬ (p = 3 ∧ q = 3))
    (he : Even ((Nat.digits 10 p).length + (Nat.digits 10 q).length)) : ¬ IsPal (p * q) := by
  intro hpal
  rw [← prod_length3 p q hp hq hdp hdq h33] at he
  have h11 := Nat.eleven_dvd_of_palindrome (pal_of_IsPal hpal) he
  rcases (Nat.Prime.dvd_mul (by norm_num)).1 h11 with h | h
  · exact not_eleven3 p hp hdp h
  · exact not_eleven3 q hq hdq h

/-- A084189, sharper: the only term of A046376 whose factors have all digits ≥ 3 is `9 = 3 * 3`. -/
theorem A084189_sharp (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpp : IsPal p) (hqp : IsPal q)
    (hdp : ∀ x ∈ Nat.digits 10 p, 3 ≤ x) (hdq : ∀ x ∈ Nat.digits 10 q, 3 ≤ x)
    (hpal : IsPal (p * q)) : p = 3 ∧ q = 3 := by
  by_contra h33
  apply not_pal_of_even3 p q hp hq hdp hdq h33 _ hpal
  have h1 : ¬ Even (Nat.digits 10 p).length := fun he =>
    not_eleven3 p hp hdp (Nat.eleven_dvd_of_palindrome (pal_of_IsPal hpp) he)
  have h2 : ¬ Even (Nat.digits 10 q).length := fun he =>
    not_eleven3 q hq hdq (Nat.eleven_dvd_of_palindrome (pal_of_IsPal hqp) he)
  rw [Nat.not_even_iff_odd] at h1 h2
  exact Odd.add_odd h1 h2

/-- A084352, sharper: the only palindromic brilliant number whose factors have all digits ≥ 3 is
`9 = 3 * 3`. -/
theorem A084352_sharp (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hlen : (Nat.digits 10 p).length = (Nat.digits 10 q).length)
    (hdp : ∀ x ∈ Nat.digits 10 p, 3 ≤ x) (hdq : ∀ x ∈ Nat.digits 10 q, 3 ≤ x)
    (hpal : IsPal (p * q)) : p = 3 ∧ q = 3 := by
  by_contra h33
  apply not_pal_of_even3 p q hp hq hdp hdq h33 _ hpal
  rw [hlen]
  exact ⟨_, rfl⟩
