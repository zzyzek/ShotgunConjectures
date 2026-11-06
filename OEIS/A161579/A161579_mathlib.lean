import Mathlib

/-
OEIS A161579, A161580, A161817, A161890, A162311 (V. Shevelev, 2009): positions n with
A010060(n) = A010060(n+k) for k = 3, 5, 9, 7, and with A010060(n) + A010060(n+3) = 1 (A161580).
Conjecture (all five entries): for fixed odd k, in the increasing sequence of n with
t(n) = t(n+k) (resp. t(n) + t(n+k) = 1), odious (t = 1) and evil (t = 0) terms alternate.

Definitions.
* `tm n = (Nat.digits 2 n).sum % 2` (A010060, Thue–Morse).

Main theorems (k odd, n < n' consecutive solutions, i.e. no solution strictly between):
* `alternate_eq`: tm n = tm (n+k), tm n' = tm (n'+k), no m in (n, n') with tm m = tm (m+k)
  ⇒ tm n ≠ tm n'.
* `alternate_ne`: the same for tm n ≠ tm (n+k) (that is, tm n + tm (n+k) = 1).

Route. With P(n) = Σ_{m<n} (-1)^tm(m): P(2j) = 0 and P(2j+1) = (-1)^tm(j) (`P_even`, `P_odd`).
Q(n) = Σ_{m<n, tm m = tm (m+k)} (-1)^tm(m) satisfies 2Q(n) = P(n) + P(n+k) - P(k) (`two_Q`), and
since n, n+k have opposite parity, Q(n) ∈ {0, -σ} with σ = P(k) = ±1 (`Q_range`). Each solution
moves Q by ±1, so consecutive solutions move it in opposite directions. Same for the other equation
with 2R(n) = P(n) - P(n+k) + P(k).
Checked: all of the above, for every odd k. Axioms: propext, Classical.choice, Quot.sound.
-/

namespace OEIS_A161579

/-- A010060 -/
def tm (n : ℕ) : ℕ := (Nat.digits 2 n).sum % 2

theorem tm_lt (n : ℕ) : tm n < 2 := Nat.mod_lt _ (by norm_num)

theorem tm_double (j : ℕ) : tm (2 * j) = tm j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rfl
  · unfold tm
    rw [Nat.digits_def' (by norm_num) (by omega)]
    simp [Nat.mul_mod_right]

theorem tm_double_add_one (j : ℕ) : tm (2 * j + 1) = 1 - tm j := by
  unfold tm
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * j + 1) % 2 = 1 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  rw [h1, h2, List.sum_cons]
  have := Nat.mod_lt ((Nat.digits 2 j).sum) (show 0 < 2 by norm_num)
  omega

def sgn (n : ℕ) : ℤ := (-1) ^ tm n

def P (n : ℕ) : ℤ := ∑ m ∈ Finset.range n, sgn m

theorem P_succ (n : ℕ) : P (n + 1) = P n + sgn n := by unfold P; rw [Finset.sum_range_succ]

theorem P_even (j : ℕ) : P (2 * j) = 0 := by
  induction j with
  | zero => simp [P]
  | succ j ih =>
    unfold P at *
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    unfold sgn
    rw [tm_double, tm_double_add_one]
    have := tm_lt j
    interval_cases (tm j) <;> norm_num

theorem P_odd (j : ℕ) : P (2 * j + 1) = sgn j := by
  unfold P
  rw [Finset.sum_range_succ]
  have := P_even j
  unfold P at this
  rw [this, zero_add]
  unfold sgn; rw [tm_double]

theorem sgn_cases (n : ℕ) : sgn n = 1 ∨ sgn n = -1 := by
  unfold sgn
  have := tm_lt n
  interval_cases (tm n) <;> simp

theorem P_cases (n : ℕ) : (Even n ∧ P n = 0) ∨ (¬ Even n ∧ (P n = 1 ∨ P n = -1)) := by
  rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
  · left; exact ⟨⟨j, by ring⟩, P_even j⟩
  · right; refine ⟨by rintro ⟨t, ht⟩; omega, ?_⟩
    rw [P_odd]; exact sgn_cases j

/-- signed count over solutions of tm m = tm (m+k) -/
def Q (k n : ℕ) : ℤ := ∑ m ∈ (Finset.range n).filter (fun m => tm m = tm (m + k)), sgn m

/-- signed count over solutions of tm m ≠ tm (m+k) -/
def R (k n : ℕ) : ℤ := ∑ m ∈ (Finset.range n).filter (fun m => tm m ≠ tm (m + k)), sgn m

theorem sgn_eq_iff (a b : ℕ) : sgn a = sgn b ↔ tm a = tm b := by
  unfold sgn
  have := tm_lt a; have := tm_lt b
  interval_cases (tm a) <;> interval_cases (tm b) <;> simp

theorem Q_succ (k n : ℕ) : Q k (n + 1) = Q k n + if tm n = tm (n + k) then sgn n else 0 := by
  unfold Q; rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert (by simp)]; ring
  · simp

theorem R_succ (k n : ℕ) : R k (n + 1) = R k n + if tm n ≠ tm (n + k) then sgn n else 0 := by
  unfold R; rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert (by simp)]; ring
  · simp

theorem two_Q (k n : ℕ) : 2 * Q k n = P n + P (n + k) - P k := by
  induction n with
  | zero => simp [Q, P]
  | succ n ih =>
    rw [Q_succ, show n + 1 + k = (n + k) + 1 by ring, P_succ, P_succ]
    split_ifs with h
    · have e := (sgn_eq_iff n (n + k)).mpr h; omega
    · have e : sgn n ≠ sgn (n + k) := fun e => h ((sgn_eq_iff n (n + k)).mp e)
      rcases sgn_cases n with h1 | h1 <;> rcases sgn_cases (n + k) with h2 | h2 <;> omega

theorem two_R (k n : ℕ) : 2 * R k n = P n - P (n + k) + P k := by
  induction n with
  | zero => simp [R, P]
  | succ n ih =>
    rw [R_succ, show n + 1 + k = (n + k) + 1 by ring, P_succ, P_succ]
    split_ifs with h
    · have e : sgn n ≠ sgn (n + k) := fun e => h ((sgn_eq_iff n (n + k)).mp e)
      rcases sgn_cases n with h1 | h1 <;> rcases sgn_cases (n + k) with h2 | h2 <;> omega
    · have e := (sgn_eq_iff n (n + k)).mpr (not_not.mp h); omega

theorem QR_range (k n : ℕ) (hk : ¬ Even k) :
    (Q k n = 0 ∨ Q k n = -P k) ∧ (R k n = 0 ∨ R k n = P k) := by
  have hQ := two_Q k n
  have hR := two_R k n
  rcases P_cases k with ⟨he, _⟩ | ⟨_, hPk⟩
  · exact absurd he hk
  rcases P_cases n with ⟨hn, hPn⟩ | ⟨hn, hPn⟩ <;> rcases P_cases (n + k) with ⟨hnk, hPnk⟩ | ⟨hnk, hPnk⟩
  · exfalso; apply hk; obtain ⟨a, ha⟩ := hn; obtain ⟨b, hb⟩ := hnk; exact ⟨b - a, by omega⟩
  · constructor <;> omega
  · constructor <;> omega
  · exfalso; apply hnk
    rcases Nat.even_or_odd n with h | ⟨a, ha⟩
    · exact absurd h hn
    rcases Nat.even_or_odd k with h | ⟨b, hb⟩
    · exact absurd h hk
    exact ⟨a + b + 1, by omega⟩

/-- consecutive solutions of `tm m = tm (m+k)` (k odd) have different `tm` -/
theorem alternate_eq (k n n' : ℕ) (hk : ¬ Even k) (hnn : n < n')
    (h1 : tm n = tm (n + k)) (h2 : tm n' = tm (n' + k))
    (hgap : ∀ m, n < m → m < n' → tm m ≠ tm (m + k)) : tm n ≠ tm n' := by
  intro heq
  have hs : sgn n = sgn n' := (sgn_eq_iff n n').mpr heq
  have hstep : ∀ j, j ≤ n' - (n + 1) → Q k (n + 1 + j) = Q k (n + 1) := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [show n + 1 + (j + 1) = (n + 1 + j) + 1 by ring, Q_succ, ih (by omega),
        ite_eq_right (hgap _ (by omega) (by omega)), add_zero]
  have hA := hstep (n' - (n + 1)) le_rfl
  rw [show n + 1 + (n' - (n + 1)) = n' by omega] at hA
  have hB := Q_succ k n'
  have hC := Q_succ k n
  rw [ite_eq_left h2] at hB; rw [ite_eq_left h1] at hC
  have r0 := (QR_range k n hk).1
  have r2 := (QR_range k (n' + 1) hk).1
  rcases P_cases k with ⟨he, _⟩ | ⟨_, hPk⟩
  · exact hk he
  rcases sgn_cases n with hs1 | hs1 <;> omega

/-- consecutive solutions of `tm m ≠ tm (m+k)` (k odd) have different `tm` -/
theorem alternate_ne (k n n' : ℕ) (hk : ¬ Even k) (hnn : n < n')
    (h1 : tm n ≠ tm (n + k)) (h2 : tm n' ≠ tm (n' + k))
    (hgap : ∀ m, n < m → m < n' → tm m = tm (m + k)) : tm n ≠ tm n' := by
  intro heq
  have hs : sgn n = sgn n' := (sgn_eq_iff n n').mpr heq
  have hstep : ∀ j, j ≤ n' - (n + 1) → R k (n + 1 + j) = R k (n + 1) := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [show n + 1 + (j + 1) = (n + 1 + j) + 1 by ring, R_succ, ih (by omega),
        ite_eq_right (not_not.mpr (hgap _ (by omega) (by omega))), add_zero]
  have hA := hstep (n' - (n + 1)) le_rfl
  rw [show n + 1 + (n' - (n + 1)) = n' by omega] at hA
  have hB := R_succ k n'
  have hC := R_succ k n
  rw [ite_eq_left h2] at hB; rw [ite_eq_left h1] at hC
  have r0 := (QR_range k n hk).2
  have r2 := (QR_range k (n' + 1) hk).2
  rcases P_cases k with ⟨he, _⟩ | ⟨_, hPk⟩
  · exact hk he
  rcases sgn_cases n with hs1 | hs1 <;> omega

end OEIS_A161579

open OEIS_A161579
