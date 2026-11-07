import Mathlib

/-
OEIS A124000: semiprimes among the binomial coefficients C(n,k), 2 <= k <= n-2.
Conjectures (entry, R. G. Wilson v, 2006): all terms except 6 and 10 are odd;
all terms except 35 are triangular numbers of the form p*(2p ± 1).

Definitions.  `Semiprime x` : x = p * q with p, q prime (p = q allowed).
`InA124000 x` : ∃ n k, 2 ≤ k, k + 2 ≤ n, x = choose n k, Semiprime x.

Main theorems.
* `A124000_char`: InA124000 x ↔ x = 35 ∨ ∃ p, p.Prime ∧
    ((2p+1).Prime ∧ x = p*(2p+1) ∨ (2p-1).Prime ∧ x = p*(2p-1)).
* `A124000_odd`: InA124000 x → x ≠ 6 → x ≠ 10 → x odd.
* `A124000_triangular`: InA124000 x → x ≠ 35 → x = p(2p±1) with p, 2p±1 prime,
  and x = choose m 2 for some m (triangular).

Route.
* `choose_le_sq`: every prime factor of choose n k is at most n
  (`Nat.pow_factorization_choose_le`), so a semiprime choose n k is at most n^2.
* `choose_three_le`: choose n 3 ≤ choose n k for 3 ≤ k ≤ n/2; and
  6 n^2 < n(n-1)(n-2) for n ≥ 9.  So 3 ≤ k ≤ n-3 forces n ≤ 8; the cases
  n = 6, 7, 8 are checked directly (only C(7,3) = C(7,4) = 35).
* `k = 2`: choose n 2 = m(2m ± 1) with coprime factors; m u = p q forces
  {m, u} = {p, q} (`two_case`).
Outside Lean: none.  Not verified in Lean: agreement with the listed data terms.
-/

def Semiprime (x : ℕ) : Prop := ∃ p q, p.Prime ∧ q.Prime ∧ x = p * q

def InA124000 (x : ℕ) : Prop :=
  ∃ n k, 2 ≤ k ∧ k + 2 ≤ n ∧ x = Nat.choose n k ∧ Semiprime x

theorem prime_le_of_dvd_choose {n k p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hd : p ∣ Nat.choose n k) (hc : 0 < Nat.choose n k) : p ≤ n := by
  have h1 := Nat.pow_factorization_choose_le (p := p) (k := k) hn
  have h2 : 1 ≤ (Nat.choose n k).factorization p :=
    (hp.dvd_iff_one_le_factorization hc.ne').mp hd
  calc p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ (Nat.choose n k).factorization p := Nat.pow_le_pow_right hp.pos h2
    _ ≤ n := h1

theorem choose_le_sq {n k : ℕ} (hn : 0 < n) (hs : Semiprime (Nat.choose n k)) :
    Nat.choose n k ≤ n * n := by
  obtain ⟨p, q, hp, hq, he⟩ := hs
  have hc : 0 < Nat.choose n k := by rw [he]; exact Nat.mul_pos hp.pos hq.pos
  have h1 : p ≤ n := prime_le_of_dvd_choose hn hp ⟨q, he⟩ hc
  have h2 : q ≤ n := prime_le_of_dvd_choose hn hq ⟨p, by rw [he, Nat.mul_comm]⟩ hc
  rw [he]; exact Nat.mul_le_mul h1 h2

theorem choose_three_le (n j : ℕ) (h : 3 + j ≤ n / 2) :
    Nat.choose n 3 ≤ Nat.choose n (3 + j) := by
  induction j with
  | zero => exact le_refl _
  | succ j ih =>
    have := ih (by omega)
    exact this.trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem big_case {n k : ℕ} (hk : 3 ≤ k) (hkn : k + 3 ≤ n)
    (hs : Semiprime (Nat.choose n k)) : n ≤ 8 := by
  by_contra hn'
  have hn : 9 ≤ n := by omega
  -- reduce to k ≤ n/2 by symmetry
  have key : ∀ k', 3 ≤ k' → k' ≤ n / 2 → Semiprime (Nat.choose n k') → False := by
    intro k' h3 h2 hs'
    have hle := choose_le_sq (by omega) hs'
    have h3le := choose_three_le n (k' - 3) (by omega)
    rw [show 3 + (k' - 3) = k' by omega] at h3le
    have hc3 : Nat.choose n 3 * 6 = n * (n - 1) * (n - 2) := by
      have := Nat.choose_mul_factorial_mul_factorial (show 3 ≤ n by omega)
      rw [show (Nat.factorial 3) = 6 by rfl] at this
      have hd := Nat.descFactorial_eq_factorial_mul_choose n 3
      rw [show (Nat.factorial 3) = 6 by rfl] at hd
      have : n.descFactorial 3 = n * (n - 1) * (n - 2) := by
        rw [show (3 : ℕ) = 0 + 1 + 1 + 1 by rfl, Nat.descFactorial_succ,
          Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_zero]
        rw [show n - (0 + 1 + 1) = n - 2 by omega, show n - (0 + 1) = n - 1 by omega,
          Nat.sub_zero]
        ring
      lia
    have hbig : 6 * (n * n) < n * (n - 1) * (n - 2) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      rw [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega]
      nlinarith
    nlinarith
  by_cases hk2 : k ≤ n / 2
  · exact key k hk hk2 hs
  · have hsym := Nat.choose_symm (show k ≤ n by omega)
    rw [← hsym] at hs
    exact key (n - k) (by omega) (by omega) hs

theorem small_case {n k : ℕ} (hk : 3 ≤ k) (hkn : k + 3 ≤ n) (hn : n ≤ 8)
    (hs : Semiprime (Nat.choose n k)) : Nat.choose n k = 35 := by
  have hle := choose_le_sq (by omega) hs
  obtain ⟨p, q, hp, hq, he⟩ := hs
  have hc : 0 < Nat.choose n k := by rw [he]; exact Nat.mul_pos hp.pos hq.pos
  have h1 : p ≤ n := prime_le_of_dvd_choose (by omega) hp ⟨q, he⟩ hc
  have h2 : q ≤ n := prime_le_of_dvd_choose (by omega) hq ⟨p, by rw [he, Nat.mul_comm]⟩ hc
  have hk5 : k ≤ 5 := by omega
  have hn6 : 6 ≤ n := by omega
  interval_cases n <;> interval_cases k <;> first | omega | rfl |
    (exfalso; norm_num [Nat.choose] at he;
     interval_cases p <;> interval_cases q <;> revert hp hq he <;> decide)

theorem two_case {m u p q : ℕ} (hm : 2 ≤ m) (hu : 2 ≤ u) (hp : p.Prime) (hq : q.Prime)
    (h : m * u = p * q) : m.Prime ∧ u.Prime := by
  have hpd : p ∣ m * u := ⟨q, h⟩
  rcases (Nat.Prime.dvd_mul hp).mp hpd with ⟨a, ha⟩ | ⟨b, hb⟩
  · subst ha
    have : a * u = q := by
      have : p * (a * u) = p * q := by rw [← h]; ring
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    rw [← this] at hq
    rcases Nat.prime_mul_iff.mp hq with ⟨_, h1⟩ | ⟨hu', ha1⟩
    · omega
    · subst ha1; simp only [Nat.mul_one]; exact ⟨hp, hu'⟩
  · subst hb
    have : m * b = q := by
      have : p * (m * b) = p * q := by rw [← h]; ring
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    rw [← this] at hq
    rcases Nat.prime_mul_iff.mp hq with ⟨hm', hb1⟩ | ⟨_, hm1⟩
    · subst hb1; simp only [Nat.mul_one]; exact ⟨hm', hp⟩
    · omega

theorem choose_two_even (m : ℕ) :
    Nat.choose (2 * m) 2 = m * (2 * m - 1) := by
  rw [Nat.choose_two_right]
  rw [show 2 * m * (2 * m - 1) = 2 * (m * (2 * m - 1)) by ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

theorem choose_two_odd (m : ℕ) :
    Nat.choose (2 * m + 1) 2 = m * (2 * m + 1) := by
  rw [Nat.choose_two_right]
  rw [show (2 * m + 1) * (2 * m + 1 - 1) = 2 * (m * (2 * m + 1)) by
    rw [show 2 * m + 1 - 1 = 2 * m by omega]; ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

def Form (x : ℕ) : Prop :=
  ∃ p, p.Prime ∧ ((2 * p + 1).Prime ∧ x = p * (2 * p + 1) ∨
    (2 * p - 1).Prime ∧ x = p * (2 * p - 1))

theorem k_two {n : ℕ} (hn : 4 ≤ n) (hs : Semiprime (Nat.choose n 2)) :
    Form (Nat.choose n 2) := by
  obtain ⟨p, q, hp, hq, he⟩ := hs
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [choose_two_even m] at he ⊢
    obtain ⟨h1, h2⟩ := two_case (by omega) (by omega) hp hq he
    exact ⟨m, h1, Or.inr ⟨h2, rfl⟩⟩
  · rw [choose_two_odd m] at he ⊢
    obtain ⟨h1, h2⟩ := two_case (by omega) (by omega) hp hq he
    exact ⟨m, h1, Or.inl ⟨h2, rfl⟩⟩

theorem A124000_char (x : ℕ) : InA124000 x ↔ x = 35 ∨ Form x := by
  constructor
  · rintro ⟨n, k, hk, hkn, rfl, hs⟩
    by_cases h2 : k = 2
    · subst h2; exact Or.inr (k_two (by omega) hs)
    by_cases h2' : k = n - 2
    · have hsym := Nat.choose_symm (show 2 ≤ n by omega)
      rw [show n - 2 = k by omega] at hsym
      rw [hsym] at hs ⊢
      exact Or.inr (k_two (by omega) hs)
    · have hn := big_case (by omega) (by omega) hs
      exact Or.inl (small_case (by omega) (by omega) hn hs)
  · rintro (rfl | ⟨p, hp, ⟨hq, rfl⟩ | ⟨hq, rfl⟩⟩)
    · refine ⟨7, 3, by omega, by omega, by decide, 5, 7, by norm_num, by norm_num, by norm_num⟩
    · have h2 := hp.two_le
      refine ⟨2 * p + 1, 2, le_refl _, by omega, (choose_two_odd p).symm, p, 2 * p + 1, hp, hq, rfl⟩
    · have h2 := hp.two_le
      refine ⟨2 * p, 2, le_refl _, by omega, (choose_two_even p).symm,
        p, 2 * p - 1, hp, hq, rfl⟩

theorem A124000_odd (x : ℕ) (hx : InA124000 x) (h6 : x ≠ 6) (h10 : x ≠ 10) : x % 2 = 1 := by
  rcases (A124000_char x).mp hx with rfl | ⟨p, hp, ⟨hq, rfl⟩ | ⟨hq, rfl⟩⟩
  · rfl
  · rcases hp.eq_two_or_odd with rfl | hodd
    · norm_num at h10
    · rw [Nat.mul_mod, hodd]; omega
  · rcases hp.eq_two_or_odd with rfl | hodd
    · norm_num at h6
    · have h2 := hp.two_le
      rw [Nat.mul_mod, hodd]; omega

theorem A124000_triangular (x : ℕ) (hx : InA124000 x) (h35 : x ≠ 35) :
    Form x ∧ ∃ m, x = Nat.choose m 2 := by
  rcases (A124000_char x).mp hx with h | hf
  · exact absurd h h35
  · refine ⟨hf, ?_⟩
    obtain ⟨p, hp, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := hf
    · exact ⟨2 * p + 1, (choose_two_odd p).symm⟩
    · exact ⟨2 * p, (choose_two_even p).symm⟩
