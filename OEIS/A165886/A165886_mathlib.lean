import Mathlib

/-
OEIS A165886: a(n) = A165641(n+1)/A165641(n), where A165641(n) = A091137(n)/A001316(n),
A091137(n) = Π_{p prime, p ≤ n+1} p^⌊n/(p-1)⌋ and A001316(n) = 2^(binary weight of n).
Conjecture (entry): a(n)/A141459(n+1) = A006519(n+1), where A141459(m) is the product of
the odd primes p with p - 1 | m and A006519(m) is the highest power of 2 dividing m.

Main theorem.
* `A165886_conjecture n : A165886 n / A141459 (n+1) = A006519 (n+1)` (in ℚ).

Route.
* `A091137_succ`: A091137(n+1) = A091137(n) · 2 · A141459(n+1), since
  ⌊(n+1)/(p-1)⌋ - ⌊n/(p-1)⌋ is 1 when p - 1 | n+1 and 0 otherwise.
* `weight_succ`: s(n) + 1 = s(n+1) + v₂(n+1) for the binary weight s (induction on n).
Checked: all of the above. Not checked: nothing beyond reading the definitions.
-/

namespace OEIS_A165886

open Finset

/-- A091137 (PARI program of the entry): Π_{p prime, p ≤ n+1} p^⌊n/(p-1)⌋. -/
def A091137 (n : ℕ) : ℕ := ∏ p ∈ (range (n + 2)).filter Nat.Prime, p ^ (n / (p - 1))

/-- A001316: 2^(sum of binary digits of n). -/
def A001316 (n : ℕ) : ℕ := 2 ^ (Nat.digits 2 n).sum

/-- A165641 = A091137 / A001316 (as a rational number). -/
def A165641 (n : ℕ) : ℚ := (A091137 n : ℚ) / A001316 n

/-- A165886: A165641(n+1) / A165641(n). -/
def A165886 (n : ℕ) : ℚ := A165641 (n + 1) / A165641 n

/-- A141459: product of the odd primes p with p - 1 ∣ n (a(0) = 1). -/
def A141459 (n : ℕ) : ℕ :=
  if n = 0 then 1 else ∏ p ∈ (range (n + 2)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ (p - 1) ∣ n), p

/-- A006519: highest power of 2 dividing n. -/
def A006519 (n : ℕ) : ℕ := 2 ^ padicValNat 2 n

theorem A091137_pos (n : ℕ) : 0 < A091137 n :=
  Finset.prod_pos (fun _ hp => pow_pos (Finset.mem_filter.mp hp).2.pos _)

theorem A141459_pos (n : ℕ) : 0 < A141459 n := by
  unfold A141459
  split_ifs
  · exact one_pos
  · exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.1.pos)

theorem filter_split (n : ℕ) :
    (range (n + 3)).filter (fun p => p.Prime ∧ (p - 1) ∣ (n + 1)) =
      insert 2 ((range (n + 3)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ (p - 1) ∣ (n + 1))) := by
  ext p
  simp only [mem_filter, mem_range, mem_insert]
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases hp : p = 2
    · exact Or.inl hp
    · exact Or.inr ⟨h1, h2, hp, h3⟩
  · rintro (rfl | ⟨h1, h2, _, h3⟩)
    · exact ⟨by omega, Nat.prime_two, by simp⟩
    · exact ⟨h1, h2, h3⟩

theorem A091137_succ (n : ℕ) : A091137 (n + 1) = A091137 n * (2 * A141459 (n + 1)) := by
  have hsub : (range (n + 2)).filter Nat.Prime ⊆ (range (n + 3)).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hext : A091137 n = ∏ p ∈ (range (n + 3)).filter Nat.Prime, p ^ (n / (p - 1)) := by
    unfold A091137
    apply Finset.prod_subset hsub
    intro p hp hnot
    simp only [mem_filter, mem_range, not_and] at hp hnot
    have : p = n + 2 := by
      by_contra h
      exact hnot (by omega) hp.2
    subst this
    simp
  have hterm : ∀ p ∈ (range (n + 3)).filter Nat.Prime,
      p ^ ((n + 1) / (p - 1)) = p ^ (n / (p - 1)) * (if (p - 1) ∣ (n + 1) then p else 1) := by
    intro p _
    rw [Nat.succ_div]
    split_ifs <;> simp [pow_succ]
  have hA : A141459 (n + 1) =
      ∏ p ∈ (range (n + 3)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ (p - 1) ∣ (n + 1)), p := by
    unfold A141459
    simp
  rw [hext, hA]
  unfold A091137
  rw [show n + 1 + 2 = n + 3 by omega, Finset.prod_congr rfl hterm, Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_filter, Finset.filter_filter, filter_split, Finset.prod_insert]
  simp

theorem sum_digits_two (m : ℕ) : (Nat.digits 2 m).sum = m % 2 + (Nat.digits 2 (m / 2)).sum := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [Nat.digits_def' (by norm_num) hm, List.sum_cons]

theorem sum_digits_even (k : ℕ) : (Nat.digits 2 (2 * k)).sum = (Nat.digits 2 k).sum := by
  rw [sum_digits_two]
  have h1 : 2 * k / 2 = k := by omega
  have h2 : 2 * k % 2 = 0 := by omega
  rw [h1, h2, zero_add]

theorem sum_digits_odd (k : ℕ) : (Nat.digits 2 (2 * k + 1)).sum = (Nat.digits 2 k).sum + 1 := by
  rw [sum_digits_two]
  have h1 : (2 * k + 1) / 2 = k := by omega
  have h2 : (2 * k + 1) % 2 = 1 := by omega
  rw [h1, h2, add_comm]

theorem weight_succ (n : ℕ) :
    (Nat.digits 2 n).sum + 1 = (Nat.digits 2 (n + 1)).sum + padicValNat 2 (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · have hodd : ¬ 2 ∣ 2 * k + 1 := by omega
      have e1 := sum_digits_even k
      have e2 := sum_digits_odd k
      rw [padicValNat.eq_zero_of_not_dvd hodd]
      omega
    · have ih' := ih k (by omega)
      have hv : padicValNat 2 (2 * k + 1 + 1) = 1 + padicValNat 2 (k + 1) := by
        rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, padicValNat.mul (by norm_num) (by omega)]
        simp
      rw [hv, sum_digits_odd, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, sum_digits_even]
      omega

theorem A165886_formula (n : ℕ) :
    A165886 n = (A141459 (n + 1) : ℚ) * A006519 (n + 1) := by
  have hw := weight_succ n
  have h0 : (A091137 n : ℚ) ≠ 0 := by exact_mod_cast (A091137_pos n).ne'
  unfold A165886 A165641 A001316 A006519
  rw [A091137_succ]
  have hpow : (2 : ℚ) ^ (Nat.digits 2 n).sum * 2 =
      2 ^ (Nat.digits 2 (n + 1)).sum * 2 ^ padicValNat 2 (n + 1) := by
    rw [← pow_add, ← pow_succ, hw]
  push_cast
  field_simp
  linear_combination (A141459 (n + 1) : ℚ) * hpow

/-- The conjecture of A165886: a(n) / A141459(n+1) = A006519(n+1). -/
theorem A165886_conjecture (n : ℕ) :
    A165886 n / A141459 (n + 1) = A006519 (n + 1) := by
  have h : (A141459 (n + 1) : ℚ) ≠ 0 := by exact_mod_cast (A141459_pos (n + 1)).ne'
  rw [A165886_formula]
  field_simp

end OEIS_A165886

open OEIS_A165886
