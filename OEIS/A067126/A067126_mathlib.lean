import Mathlib

/-
OEIS A067126: numbers n with phi(n) >= phi(k) for all k = 1 .. n-1.
Conjecture (A. Murthy, 2002): 4 and 9 are the only composite terms.

Checked here.
* `A067126_totient_add_div_le`: phi(n) + n/q <= n for every prime q dividing n.
* `A067126_gap`: if n > 1 is a composite term and p < n is prime, then
  sqrt(n) <= n - p + 1.  So a composite term n lies at distance at least
  sqrt(n) - 1 above the largest prime below it: the gap after that prime exceeds sqrt(n) - 1.
* `A067126_four`, `A067126_nine`: 4 and 9 are terms.
* `A067126_square_term`: if q is prime and no prime lies in [q^2 - q + 2, q^2 - 1], then q^2 is a
  term.  So the conjecture implies: for every prime q >= 5 there is a prime in (q^2 - q + 1, q^2),
  the lower half of Oppermann's conjecture at prime arguments.

Not checked here: the prime-gap data that excludes composite terms in a range.
-/

open Finset

theorem A067126_totient_add_div_le (n q : ℕ) (hq : q.Prime) (hqn : q ∣ n) :
    Nat.totient n + n / q ≤ n := by
  rw [Nat.totient_eq_card_coprime]
  set A := (range n).filter (fun a => n.Coprime a) with hA
  set B := (range (n / q)).image (fun j => q * j) with hB
  have hBc : B.card = n / q := by
    rw [hB, card_image_of_injective _ (mul_right_injective₀ hq.ne_zero), card_range]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rw [hA, mem_filter] at hxA
    rw [hB, mem_image] at hxB
    obtain ⟨j, -, rfl⟩ := hxB
    have h1 : Nat.Coprime n q := Nat.Coprime.coprime_mul_right_right hxA.2
    have h2 : q = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm h1) hqn
    exact hq.one_lt.ne' h2
  have hsub : A ∪ B ⊆ range n := by
    intro x hx
    rcases mem_union.mp hx with h | h
    · exact (mem_filter.mp h).1
    · rw [hB, mem_image] at h
      obtain ⟨j, hj, rfl⟩ := h
      rw [mem_range] at hj ⊢
      calc q * j < q * (n / q) := Nat.mul_lt_mul_of_pos_left hj hq.pos
        _ ≤ n := Nat.mul_div_le n q
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj, hBc, card_range] at this
  exact this

theorem A067126_gap (n p : ℕ) (hn1 : 1 < n) (hcomp : ¬ n.Prime)
    (hterm : ∀ k < n, Nat.totient k ≤ Nat.totient n) (hp : p.Prime) (hpn : p < n) :
    Nat.sqrt n ≤ n - p + 1 := by
  set q := n.minFac with hqdef
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hqn : q ∣ n := Nat.minFac_dvd n
  have hsq : q ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hcomp
  have h1 := A067126_totient_add_div_le n q hq hqn
  have h2 : Nat.totient p ≤ Nat.totient n := hterm p hpn
  rw [Nat.totient_prime hp] at h2
  have hqs : q ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by nlinarith)
  have hs : Nat.sqrt n ≤ n / q := by
    rw [Nat.le_div_iff_mul_le hq.pos]
    calc Nat.sqrt n * q ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul_left _ hqs
      _ ≤ n := Nat.sqrt_le n
  have hp1 : 1 ≤ p := hp.one_lt.le
  omega

theorem A067126_four : ∀ k < 4, Nat.totient k ≤ Nat.totient 4 := by decide

theorem A067126_nine : ∀ k < 9, Nat.totient k ≤ Nat.totient 9 := by decide

theorem A067126_composite_bound (k : ℕ) (hk : 1 < k) (hc : ¬ k.Prime) :
    Nat.totient k + Nat.sqrt k ≤ k := by
  set r := k.minFac with hr
  have hrp : r.Prime := Nat.minFac_prime (by omega)
  have hrk : r ∣ k := Nat.minFac_dvd k
  have hsq : r ^ 2 ≤ k := Nat.minFac_sq_le_self (by omega) hc
  have h1 := A067126_totient_add_div_le k r hrp hrk
  have hrs : r ≤ Nat.sqrt k := Nat.le_sqrt.mpr (by nlinarith)
  have hs : Nat.sqrt k ≤ k / r := by
    rw [Nat.le_div_iff_mul_le hrp.pos]
    calc Nat.sqrt k * r ≤ Nat.sqrt k * Nat.sqrt k := Nat.mul_le_mul_left _ hrs
      _ ≤ k := Nat.sqrt_le k
  omega

theorem A067126_square_term (q : ℕ) (hq : q.Prime)
    (hgap : ∀ m, q ^ 2 - q + 2 ≤ m → m < q ^ 2 → ¬ m.Prime) :
    ∀ k < q ^ 2, Nat.totient k ≤ Nat.totient (q ^ 2) := by
  intro k hk
  have hq2 : 2 ≤ q := hq.two_le
  have htq : Nat.totient (q ^ 2) = q * (q - 1) := by
    rw [Nat.totient_prime_pow hq (by norm_num)]; ring_nf
  rw [htq]
  have hQ : q ^ 2 = q * q := by ring
  have hQ1 : q * (q - 1) + q = q * q := by
    cases q with
    | zero => omega
    | succ t => simp; ring
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have : Nat.totient k ≤ 1 := by interval_cases k <;> simp
    have : 1 ≤ q * (q - 1) := Nat.one_le_iff_ne_zero.mpr (by
      apply Nat.mul_ne_zero <;> omega)
    omega
  by_cases hkp : k.Prime
  · rw [Nat.totient_prime hkp]
    have : ¬ (q ^ 2 - q + 2 ≤ k) := fun h => hgap k h hk hkp
    omega
  · have hb := A067126_composite_bound k (by omega) hkp
    by_cases hsmall : k ≤ q * (q - 1)
    · omega
    · have hge : (q - 1) * (q - 1) ≤ k := by
        have : (q - 1) * (q - 1) ≤ q * (q - 1) := Nat.mul_le_mul_right _ (by omega)
        omega
      have hs : q - 1 ≤ Nat.sqrt k := Nat.le_sqrt.mpr hge
      omega
