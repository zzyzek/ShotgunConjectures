import Mathlib

/-
OEIS A227864: smallest base in which n's digital reversal is prime, or 0 if no
such base exists.
Conjecture 2 (entry): n = 2 is the only prime p which must be represented in
base p + 1 for its reversal to be prime.
Conjecture 3 (entry): with the restriction gcd(base, n) = 1, a(n) = 0 except
for n = 2, 3 and n = 6k +- 1.

Definitions.  `rev b n` is the number whose base-b digits are those of n in
reverse order: `Nat.ofDigits b (Nat.digits b n).reverse` (Mathlib's
`Nat.digits` lists digits least significant first, without leading zeros).

Main theorem.
* `A227864_conj3`: if 2 | n or 3 | n, n is not 2 or 3, b >= 2 and
  gcd(b, n) = 1, then `rev b n` is not prime.  So the restricted a(n) is 0
  for every n outside {2, 3} and the numbers 6k +- 1 (n = 0 and n = 1 give 0
  trivially).  This is the "a(n) = 0" half of Conjecture 3, read as stated.
  The other half (a(n) > 0 for each 6k +- 1 >= 5, i.e. a coprime base with a
  prime reversal exists) is not proved here; for prime n it holds with base
  n + 1.

* `A227864_conj2`: every prime p >= 3 has prime reversal in base p - 1
  (p is written 11 there), so p = 2 is the only prime whose smallest base is
  p + 1 (Conjecture 2).  `rev_succ` is the computation.
Conjecture 1 (no base for n other than 0, 1, 4) is not proved here.

Route.
* `ofDigits_reverse`: if c * c = 1 in a commutative ring, then
  ofDigits c L.reverse = c^(|L|+1) * ofDigits c L.
* `dvd_rev`: for q in {2, 3} with q | n and q not dividing b, (b : ZMod q)
  squares to 1, so q | rev b n.
* `rev_rev`: when b does not divide n, the digits of rev b n are the reversed
  digits of n, so rev b (rev b n) = n.  A prime rev b n divisible by q equals
  q, so n = rev b q = q.

Checked: everything above.  Not checked: nothing beyond reading the entry.
-/

def rev (b n : ℕ) : ℕ := Nat.ofDigits b (Nat.digits b n).reverse

lemma ofDigits_app {R : Type*} [CommRing R] (c : R) :
    ∀ L1 L2 : List ℕ, Nat.ofDigits c (L1 ++ L2) =
      Nat.ofDigits c L1 + c ^ L1.length * Nat.ofDigits c L2
  | [], L2 => by simp [Nat.ofDigits]
  | a :: L1, L2 => by
    simp only [List.cons_append, Nat.ofDigits, ofDigits_app c L1 L2, List.length_cons]
    ring

lemma ofDigits_reverse {R : Type*} [CommRing R] (c : R) (hc : c * c = 1) :
    ∀ L : List ℕ, Nat.ofDigits c L.reverse = c ^ (L.length + 1) * Nat.ofDigits c L := by
  intro L
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons a L ih =>
    rw [List.reverse_cons, ofDigits_app, ih, List.length_reverse]
    simp only [Nat.ofDigits, List.length_cons]
    linear_combination (-(c ^ L.length * (a : R)) - c ^ (L.length + 1) * Nat.ofDigits c L) * hc

lemma dvd_rev (q b n : ℕ) (hq : ∀ x : ZMod q, x ≠ 0 → x * x = 1)
    (hqn : q ∣ n) (hqb : ¬ q ∣ b) : q ∣ rev b n := by
  have hb0 : (b : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqb
  have hcast : ((rev b n : ℕ) : ZMod q) = 0 := by
    rw [rev, Nat.coe_ofDigits, ofDigits_reverse _ (hq _ hb0), ← Nat.coe_ofDigits,
      Nat.ofDigits_digits, (ZMod.natCast_eq_zero_iff n q).mpr hqn, mul_zero]
  exact (ZMod.natCast_eq_zero_iff _ _).mp hcast

lemma rev_rev (b n : ℕ) (hb : 2 ≤ b) (hn : 0 < n) (hbn : ¬ b ∣ n) :
    rev b (rev b n) = n := by
  have hd : Nat.digits b (rev b n) = (Nat.digits b n).reverse := by
    rw [rev]
    apply Nat.digits_ofDigits b (by omega)
    · intro l hl
      rw [List.mem_reverse] at hl
      exact Nat.digits_lt_base (by omega) hl
    · intro h
      rw [List.getLast_reverse]
      have key : ∀ (L : List ℕ) (h : L ≠ []),
          L = (n % b) :: Nat.digits b (n / b) → L.head h = n % b := by
        intro L h e; subst e; rfl
      rw [key _ _ (Nat.digits_def' (by omega) hn)]
      intro h0
      exact hbn (Nat.dvd_of_mod_eq_zero h0)
  rw [rev, hd, List.reverse_reverse, Nat.ofDigits_digits]

lemma rev_small (b q : ℕ) (hb : 2 ≤ b) (hq : q = 2 ∨ q = 3) (hqb : ¬ q ∣ b) :
    rev b q = q := by
  rcases Nat.lt_or_ge q b with h | h
  · rw [rev, Nat.digits_of_lt b q (by omega) h]
    simp
  · have : b = 2 ∧ q = 3 := by
      rcases hq with rfl | rfl
      · exact absurd (by interval_cases b; norm_num) hqb
      · interval_cases b
        · exact ⟨rfl, rfl⟩
        · exact absurd (dvd_refl 3) hqb
    obtain ⟨rfl, rfl⟩ := this
    decide

lemma no_prime_rev (q b n : ℕ) (hq2 : q = 2 ∨ q = 3)
    (hq : ∀ x : ZMod q, x ≠ 0 → x * x = 1)
    (hb : 2 ≤ b) (hcop : Nat.Coprime b n) (hqn : q ∣ n) (hnq : n ≠ q) :
    ¬ (rev b n).Prime := by
  intro hp
  have hqb : ¬ q ∣ b := by
    intro h
    have := Nat.dvd_gcd h hqn
    rw [hcop] at this
    rcases hq2 with rfl | rfl <;> omega
  have hd := dvd_rev q b n hq hqn hqb
  have hrq : rev b n = q := by
    rcases hp.eq_one_or_self_of_dvd q hd with h | h
    · rcases hq2 with rfl | rfl <;> omega
    · exact h.symm
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      rw [Nat.coprime_zero_right] at hcop
      omega
    · exact h
  have hbn : ¬ b ∣ n := by
    intro h
    have := Nat.dvd_gcd (dvd_refl b) h
    rw [hcop] at this
    have := Nat.le_of_dvd one_pos this
    omega
  have := rev_rev b n hb hn0 hbn
  rw [hrq, rev_small b q hb hq2 hqb] at this
  exact hnq this.symm

theorem A227864_conj3 (b n : ℕ) (hb : 2 ≤ b) (hcop : Nat.Coprime b n)
    (h23 : 2 ∣ n ∨ 3 ∣ n) (hn2 : n ≠ 2) (hn3 : n ≠ 3) :
    ¬ (rev b n).Prime := by
  rcases h23 with h | h
  · exact no_prime_rev 2 b n (Or.inl rfl) (by decide) hb hcop h hn2
  · exact no_prime_rev 3 b n (Or.inr rfl) (by decide) hb hcop h hn3

/-- The entry's example: 9 in base 6 is 13, reversed 31 = 19 (decimal). -/
theorem rev_6_9 : rev 6 9 = 19 := by decide

/-- In base b >= 2, b + 1 is written 11, so it is its own reversal. -/
lemma rev_succ (b : ℕ) (hb : 2 ≤ b) : rev b (b + 1) = b + 1 := by
  have h1 : (b + 1) % b = 1 := by
    rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt (by omega)
  have h2 : (b + 1) / b = 1 := by
    rw [Nat.add_div_left _ (by omega), Nat.div_eq_of_lt (by omega)]
  have hd : Nat.digits b (b + 1) = [1, 1] := by
    rw [Nat.digits_def' (by omega) (by omega), h1, h2, Nat.digits_of_lt b 1 (by omega) (by omega)]
  rw [rev, hd]
  simp [Nat.ofDigits]
  ring

/-- Conjecture 2: every prime p >= 3 has a base b <= p - 1 (namely b = p - 1)
in which its reversal is prime; so p = 2 is the only prime needing base p + 1. -/
theorem A227864_conj2 (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) :
    2 ≤ p - 1 ∧ (rev (p - 1) p).Prime := by
  refine ⟨by omega, ?_⟩
  have := rev_succ (p - 1) (by omega)
  rw [show p - 1 + 1 = p by omega] at this
  rw [this]; exact hp
