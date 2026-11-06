import Mathlib

/-
OEIS A187941: a(n) = least number with exactly n even divisors (offset 0).
Conjecture (entry): "a(n) = 2^n only if n is prime or if n = 1."

Definitions.
* `evenDivs m` = number of even divisors of m.
* `a n` = least m ≥ 1 with `evenDivs m = n` (exists: m = 2^n).

Main theorems.
* `A187941_main (n) (hn : 1 ≤ n) : a n = 2 ^ n ↔ n.Prime ∨ n = 1`.
* `A187941_zero : a 0 = 2 ^ 0 ∧ ¬ (Nat.Prime 0 ∨ 0 = 1)`: at the offset n = 0 the literal
  statement fails (a(0) = 1 = 2^0).

Route. Even divisors of 2y are 2·(divisors of y), so evenDivs (2y) = d(y), and odd m has none.
For n prime (or 1) any m with n even divisors is 2y with d(y) = n, and d(y) prime forces
y = q^(n-1) with q prime, so m ≥ 2^n. For composite n = a·b (2 ≤ a, b) the number
2^a·3^(b-1) has n even divisors and is < 2^n.
Checked: all of the above. Not checked: nothing beyond reading "least number" as least m ≥ 1.
Axioms: propext, Classical.choice, Quot.sound.
-/

namespace OEIS_A187941

/-- number of even divisors -/
def evenDivs (m : ℕ) : ℕ := ((Nat.divisors m).filter Even).card

theorem evenDivs_two_mul (y : ℕ) (hy : y ≠ 0) : evenDivs (2 * y) = (Nat.divisors y).card := by
  unfold evenDivs
  have e : (Nat.divisors (2 * y)).filter Even =
      (Nat.divisors y).map ⟨fun x => x + x, fun a b h => by simp only at h; omega⟩ := by
    ext x
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_map]
    constructor
    · rintro ⟨⟨hd, -⟩, ⟨z, rfl⟩⟩
      refine ⟨z, ⟨?_, hy⟩, rfl⟩
      have h2 : 2 * z ∣ 2 * y := by rwa [two_mul]
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
    · rintro ⟨z, ⟨hz, -⟩, rfl⟩
      refine ⟨⟨?_, by omega⟩, ⟨z, rfl⟩⟩
      show z + z ∣ 2 * y
      rw [← two_mul]; exact Nat.mul_dvd_mul_left 2 hz
  rw [e, Finset.card_map]

theorem evenDivs_odd (m : ℕ) (hm : ¬ 2 ∣ m) : evenDivs m = 0 := by
  unfold evenDivs
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx hE
  exact hm ((even_iff_two_dvd.mp hE).trans (Nat.dvd_of_mem_divisors hx))

theorem card_divisors_prime_pow' (q k : ℕ) (hq : q.Prime) : (Nat.divisors (q ^ k)).card = k + 1 := by
  rw [Nat.divisors_prime_pow hq, Finset.card_map, Finset.card_range]

theorem evenDivs_pow (n : ℕ) : evenDivs (2 ^ n) = n := by
  rcases n with _ | k
  · exact evenDivs_odd 1 (by norm_num)
  · rw [pow_succ', evenDivs_two_mul _ (by positivity), card_divisors_prime_pow' 2 k Nat.prime_two]

theorem exists_m (n : ℕ) : ∃ m, 0 < m ∧ evenDivs m = n := ⟨2 ^ n, by positivity, evenDivs_pow n⟩

/-- A187941: least m ≥ 1 with exactly n even divisors -/
noncomputable def a (n : ℕ) : ℕ := Nat.find (exists_m n)

theorem card_divisors_eq_one (r : ℕ) (hr : r ≠ 0) (h : (Nat.divisors r).card = 1) : r = 1 := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h
  have h1 : 1 ∈ Nat.divisors r := Nat.mem_divisors.mpr ⟨one_dvd r, hr⟩
  have h2 : r ∈ Nat.divisors r := Nat.mem_divisors.mpr ⟨dvd_refl r, hr⟩
  rw [hx, Finset.mem_singleton] at h1 h2
  omega

/-- d(y) = p prime forces y = q^(p-1), so y ≥ 2^(p-1). -/
theorem prime_card (y p : ℕ) (hy : y ≠ 0) (hp : p.Prime) (h : (Nat.divisors y).card = p) :
    2 ^ (p - 1) ≤ y := by
  have hy1 : y ≠ 1 := by
    rintro rfl; simp at h; exact hp.one_lt.ne' h.symm
  have hq : (Nat.minFac y).Prime := Nat.minFac_prime hy1
  obtain ⟨e, r, hr, hyr⟩ := Nat.exists_eq_pow_mul_and_not_dvd hy (Nat.minFac y) hq.ne_one
  have hcop : (Nat.minFac y ^ e).Coprime r :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hq).mpr hr)
  have hr0 : r ≠ 0 := by rintro rfl; simp at hyr; exact hy hyr
  have he : e ≠ 0 := by
    rintro rfl
    simp at hyr
    exact hr (hyr ▸ Nat.minFac_dvd y)
  rw [hyr, Nat.Coprime.card_divisors_mul hcop, card_divisors_prime_pow' _ _ hq] at h
  rw [← h] at hp
  rcases Nat.prime_mul_iff.mp hp with ⟨-, h1⟩ | ⟨-, h1⟩
  · have := card_divisors_eq_one r hr0 h1
    rw [hyr, this, mul_one, ← h, h1, mul_one, Nat.add_sub_cancel]
    exact Nat.pow_le_pow_left hq.two_le e
  · omega

theorem a_spec (n : ℕ) : 0 < a n ∧ evenDivs (a n) = n := Nat.find_spec (exists_m n)

theorem a_le (n m : ℕ) (hm : 0 < m) (h : evenDivs m = n) : a n ≤ m := Nat.find_min' _ ⟨hm, h⟩

/-- Main theorem: for n ≥ 1, a(n) = 2^n exactly when n is prime or n = 1. -/
theorem A187941_main (n : ℕ) (hn : 1 ≤ n) : a n = 2 ^ n ↔ n.Prime ∨ n = 1 := by
  constructor
  · intro heq
    by_contra hc
    simp only [not_or] at hc
    obtain ⟨hnp, hn1⟩ := hc
    have hn2 : 2 ≤ n := by omega
    -- n = u * v with 2 ≤ u, 2 ≤ v
    have hu2 : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
    have hult : n.minFac < n := (Nat.not_prime_iff_minFac_lt hn2).mp hnp
    obtain ⟨v, hv⟩ := Nat.minFac_dvd n
    generalize n.minFac = u at hu2 hult hv
    have hv2 : 2 ≤ v := by
      rcases v with _ | _ | v <;> (try simp at hv) <;> omega
    obtain ⟨c, rfl⟩ : ∃ c, v = c + 2 := ⟨v - 2, by omega⟩
    obtain ⟨d, hd⟩ : ∃ d, u = d + 1 := ⟨u - 1, by omega⟩
    set w := 2 ^ u * 3 ^ (c + 1) with hw
    have hwe : evenDivs w = n := by
      have e : w = 2 * (2 ^ d * 3 ^ (c + 1)) := by rw [hw, hd, pow_succ]; ring
      rw [e, evenDivs_two_mul _ (by positivity),
        Nat.Coprime.card_divisors_mul (Nat.Coprime.pow _ _ (by norm_num)),
        card_divisors_prime_pow' 2 d Nat.prime_two, card_divisors_prime_pow' 3 _ Nat.prime_three,
        hv, hd]
    have hlt : w < 2 ^ n := by
      have h1 : 3 ^ (c + 1) < 4 ^ (c + 1) := Nat.pow_lt_pow_left (by norm_num) (by omega)
      have h2 : 4 ^ (c + 1) ≤ 2 ^ (u * (c + 1)) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hu2)
      have h3 : 2 ^ u * 2 ^ (u * (c + 1)) = 2 ^ n := by
        rw [← pow_add, hv]; congr 1; ring
      calc w = 2 ^ u * 3 ^ (c + 1) := hw
        _ < 2 ^ u * 2 ^ (u * (c + 1)) :=
            Nat.mul_lt_mul_of_pos_left (lt_of_lt_of_le h1 h2) (by positivity)
        _ = 2 ^ n := h3
    have := a_le n w (by positivity) hwe
    omega
  · intro hpn
    apply le_antisymm (a_le n _ (by positivity) (evenDivs_pow n))
    obtain ⟨hpos, hev⟩ := a_spec n
    have h2 : 2 ∣ a n := by
      by_contra h; rw [evenDivs_odd _ h] at hev; omega
    obtain ⟨y, hy⟩ := h2
    have hy0 : y ≠ 0 := by rintro rfl; omega
    rw [hy, evenDivs_two_mul y hy0] at hev
    have hlow : 2 ^ (n - 1) ≤ y := by
      rcases hpn with hp | rfl
      · exact prime_card y n hy0 hp hev
      · simp; omega
    rw [hy]
    calc 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
      _ ≤ 2 * y := Nat.mul_le_mul_left 2 hlow

/-- At the offset n = 0 the literal statement fails: a(0) = 1 = 2^0. -/
theorem A187941_zero : a 0 = 2 ^ 0 ∧ ¬ (Nat.Prime 0 ∨ 0 = 1) := by
  refine ⟨?_, by simp [Nat.not_prime_zero]⟩
  apply le_antisymm (a_le 0 1 (by norm_num) (evenDivs_odd 1 (by norm_num)))
  exact (a_spec 0).1

end OEIS_A187941

open OEIS_A187941
