import Mathlib

/-
OEIS A137328 (Mathlib): a(n) = prime(n) - primorial(k), k maximal with primorial(k) ≤ prime(n),
where primorial(k) is the product of the first k primes. Conjecture: every prime occurs.
README result: false, 2 never occurs.

Main theorem `A137328_main`: with `pk k = ∏ i < k, Nat.nth Nat.Prime i` (product of the first
k primes; `Nat.nth` is 0-indexed, so this is primorial(k)) and p = `Nat.nth Nat.Prime n`, for
every k with pk k ≤ p < pk (k + 1), p - pk k ≠ 2. Since pk is strictly increasing, these k
are exactly the maximal k of the definition, so a(n) ≠ 2 for every n.
`A137328_conjecture_false`: 2 is prime and is not a(n) for any n.

Proof. pk 1 = 2 ≤ p, so k ≥ 1; then pk k is even (factor nth Prime 0 = 2) and ≥ 2, and
p = pk k + 2 would be even and ≥ 4.

Outside Lean: nothing.
-/

open Finset

/-- Product of the first k primes. -/
noncomputable def A137328_pk (k : ℕ) : ℕ := ∏ i ∈ range k, Nat.nth Nat.Prime i

theorem A137328_main (n k : ℕ) (h1 : A137328_pk k ≤ Nat.nth Nat.Prime n)
    (h2 : Nat.nth Nat.Prime n < A137328_pk (k + 1)) :
    Nat.nth Nat.Prime n - A137328_pk k ≠ 2 := by
  have hp := Nat.prime_nth_prime n
  have hk : k ≠ 0 := by
    rintro rfl
    simp [A137328_pk, Nat.nth_prime_zero_eq_two] at h2
    have := hp.two_le
    omega
  have hdvd : 2 ∣ A137328_pk k := by
    have := Finset.dvd_prod_of_mem (fun i => Nat.nth Nat.Prime i)
      (Finset.mem_range.mpr (Nat.pos_of_ne_zero hk))
    simpa [A137328_pk, Nat.nth_prime_zero_eq_two] using this
  have hpos : 0 < A137328_pk k :=
    Finset.prod_pos (fun i _ => (Nat.prime_nth_prime i).pos)
  intro he
  have h2le : 2 ≤ A137328_pk k := by
    obtain ⟨c, hc⟩ := hdvd
    omega
  have hd2 : 2 ∣ Nat.nth Nat.Prime n := by
    obtain ⟨c, hc⟩ := hdvd
    exact ⟨c + 1, by omega⟩
  rcases hp.eq_one_or_self_of_dvd 2 hd2 with h | h <;> omega

/-- The maximal k exists for every n (pk 0 = 1 ≤ p and pk is unbounded). -/
theorem A137328_exists_k (n : ℕ) :
    ∃ k, A137328_pk k ≤ Nat.nth Nat.Prime n ∧ Nat.nth Nat.Prime n < A137328_pk (k + 1) := by
  have hge : ∀ k, k ≤ A137328_pk k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [A137328_pk, Finset.prod_range_succ, ← A137328_pk]
      have h2 := (Nat.prime_nth_prime k).two_le
      have hpos : 0 < A137328_pk k :=
        Finset.prod_pos (fun i _ => (Nat.prime_nth_prime i).pos)
      nlinarith
  classical
  let p := Nat.nth Nat.Prime n
  have hex : ∃ k, p < A137328_pk k := ⟨p + 1, by have := hge (p + 1); omega⟩
  let k0 := Nat.find hex
  have hk0 : p < A137328_pk k0 := Nat.find_spec hex
  have hk0' : k0 ≠ 0 := by
    intro h
    have : p < A137328_pk 0 := h ▸ hk0
    simp [A137328_pk] at this
    have := (Nat.prime_nth_prime n).two_le
    omega
  obtain ⟨k, hk⟩ : ∃ k, k0 = k + 1 := ⟨k0 - 1, by omega⟩
  refine ⟨k, ?_, hk ▸ hk0⟩
  have := Nat.find_min hex (show k < k0 by omega)
  omega

theorem A137328_conjecture_false : Nat.Prime 2 ∧ ∀ n k : ℕ,
    A137328_pk k ≤ Nat.nth Nat.Prime n → Nat.nth Nat.Prime n < A137328_pk (k + 1) →
    Nat.nth Nat.Prime n - A137328_pk k ≠ 2 :=
  ⟨Nat.prime_two, A137328_main⟩
