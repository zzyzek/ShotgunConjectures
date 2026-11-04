/-
OEIS A000120 (binary weight). Conjecture (OEIS wiki Talk:Conjectures/List,
A000120 line 19): write the base-b digit sum s_b (b ≥ 2) as a triangle with
row 0 = s_b(0) and row r ≥ 1 = s_b(b^(r-1)), ..., s_b(b^r - 1); then all
positive entries of each column k are equal.  True (trivial).

Column k of row r = j + 1 is s_b(b^j + k), present exactly when
k < b^(j+1) - b^j = (b-1)·b^j.

Checked here (core Lean, full statement):
* `ds_split`: s_b(b^j·t + k) = s_b(t) + s_b(k) for k < b^j.
* `column`: s_b(b^j + k) = 1 + s_b(k) whenever k < (b-1)·b^j, i.e. every
  entry of column k in a row r ≥ 1 equals 1 + s_b(k), independent of r.
  (Row 0 holds the single value 0, the only non-positive entry.)
Not checked here: nothing.
-/

def ds (b : Nat) (n : Nat) : Nat :=
  if _h : 0 < n ∧ 1 < b then n % b + ds b (n / b) else 0
termination_by n
decreasing_by exact Nat.div_lt_self _h.1 _h.2

theorem ds_zero (b : Nat) : ds b 0 = 0 := by
  rw [ds]; simp

theorem ds_step (b q r : Nat) (hb : 1 < b) (hr : r < b) :
    ds b (b * q + r) = r + ds b q := by
  by_cases h0 : b * q + r = 0
  · have hq : q = 0 := by
      rcases Nat.eq_zero_of_add_eq_zero h0 with ⟨h1, _⟩
      rcases Nat.mul_eq_zero.mp h1 with h | h
      · omega
      · exact h
    have : r = 0 := by omega
    subst hq; subst this; simp [ds_zero]
  · rw [ds, dite_eq_left ⟨by omega, hb⟩, Nat.mul_add_mod, Nat.mod_eq_of_lt hr,
        Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]

theorem ds_digit (b d : Nat) (hb : 1 < b) (hd : d < b) : ds b d = d := by
  have := ds_step b 0 d hb hd
  simpa [ds_zero] using this

theorem ds_split (b : Nat) (hb : 1 < b) :
    ∀ j t k, k < b ^ j → ds b (b ^ j * t + k) = ds b t + ds b k := by
  intro j
  induction j with
  | zero =>
    intro t k hk
    have : k = 0 := by simp at hk; omega
    subst this; simp [ds_zero]
  | succ j ih =>
    intro t k hk
    have hb0 : 0 < b := by omega
    have hkb : k / b < b ^ j := by
      apply (Nat.div_lt_iff_lt_mul hb0).mpr
      rw [Nat.pow_succ] at hk; exact hk
    have e : b ^ (j + 1) * t + k = b * (b ^ j * t + k / b) + k % b := by
      have hk' := Nat.div_add_mod k b
      rw [Nat.pow_succ]
      calc b ^ j * b * t + k = b ^ j * b * t + (b * (k / b) + k % b) := by rw [hk']
        _ = b * (b ^ j * t + k / b) + k % b := by
          rw [Nat.mul_add, Nat.mul_comm (b ^ j) b, Nat.mul_assoc, Nat.add_assoc]
    have ek : ds b k = k % b + ds b (k / b) := by
      have := ds_step b (k / b) (k % b) hb (Nat.mod_lt _ hb0)
      rw [Nat.div_add_mod] at this; exact this
    rw [e, ds_step b _ _ hb (Nat.mod_lt _ hb0), ih t (k / b) hkb, ek]
    omega

theorem column (b j k : Nat) (hb : 1 < b) (hk : k < (b - 1) * b ^ j) :
    ds b (b ^ j + k) = 1 + ds b k := by
  have hp : 0 < b ^ j := Nat.pow_pos (by omega)
  have ht : k / b ^ j < b - 1 := (Nat.div_lt_iff_lt_mul hp).mpr hk
  have e1 : b ^ j + k = b ^ j * (k / b ^ j + 1) + k % b ^ j := by
    have := Nat.div_add_mod k (b ^ j)
    rw [Nat.mul_add, Nat.mul_one]; omega
  have e2 : k = b ^ j * (k / b ^ j) + k % b ^ j := (Nat.div_add_mod k (b ^ j)).symm
  have hm : k % b ^ j < b ^ j := Nat.mod_lt _ hp
  rw [e1, ds_split b hb j _ _ hm, ds_digit b _ hb (by omega)]
  conv => rhs; rw [e2, ds_split b hb j _ _ hm, ds_digit b _ hb (by omega)]
  omega
