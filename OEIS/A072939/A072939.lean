/-
OEIS A072939: c(1) = 1, c(2) = n, c(k+2) = (c(k+1) + c(k))/2 if c(k+1) and
c(k) have the same parity, else |c(k+1) - 2 c(k)|; the sequence lists the
n with lim c(k) = infinity. Conjecture (V. Jovovic, 2003):
a(n) = A036554(n) + 1, where A036554 lists the numbers whose binary
expansion ends in an odd number of zeros.

Here `A072939_c n k` is c(k+1) (so `A072939_c n 0 = 1`, `A072939_c n 1 = n`),
computed by iterating the pair map `A072939_T (a, b) = (b, step a b)`.

Main theorem `A072939_main`: for n ≥ 1, c(k) → ∞ iff
n = 2^(2j+1) (2u+1) + 1 for some j, u, i.e. iff n - 1 is positive with odd
2-adic valuation, i.e. iff n - 1 is in A036554. Listing both sets in
increasing order gives a(n) = A036554(n) + 1.

Route. With up(a, E) = (a, a+E) and down(b, E) = (b+E, b):
* `A072939_halve`: up(a, 2D) ↦ down(a+D, D) and down(a, 2D) ↦ up(a, D), so
  after v steps up(1, 2^v u) becomes up(1+cu, u) (v even) or
  down(1+cu, u) (v odd), u odd.
* `A072939_down_iter`: for odd m, two steps take down(b, m) to
  down(b+m, m), so c(k) ≥ (k - k0)/2 → ∞.
* `A072939_asc`, `A072939_gap1`: for odd u, up(1+cu, u) reaches (1, 1)
  (two steps take up(x, u) to up(x-u, u) for x > u, up(1, u) to
  up(u-1, 1), and up(x, 1) to up(x-1, 1)); (1, 1) is fixed.

Not checked: that `A072939_step` transcribes the entry's rule (it does:
|b - 2a| is written by cases), and the step from set equality to the
index shift of the two increasing listings. The value n = 0 (also
divergent: 1, 0, 2, 1, 3, 2, ...) is outside the entry's range.
-/

def A072939_step (a b : Nat) : Nat :=
  if a % 2 = b % 2 then (a + b) / 2 else (if 2 * a ≤ b then b - 2 * a else 2 * a - b)


def A072939_T (p : Nat × Nat) : Nat × Nat := (p.2, A072939_step p.1 p.2)

/-- k-fold iterate of the pair map. -/
def A072939_it (p : Nat × Nat) : Nat → Nat × Nat
  | 0 => p
  | k + 1 => A072939_T (A072939_it p k)

theorem A072939_step_same (a b : Nat) (h : a % 2 = b % 2) : A072939_step a b = (a + b) / 2 := by
  simp [A072939_step, h]

theorem A072939_step_up (a b : Nat) (h : a % 2 ≠ b % 2) (h2 : 2 * a ≤ b) :
    A072939_step a b = b - 2 * a := by
  simp [A072939_step, h, h2]

theorem A072939_step_dn (a b : Nat) (h : a % 2 ≠ b % 2) (h2 : ¬ 2 * a ≤ b) :
    A072939_step a b = 2 * a - b := by
  simp [A072939_step, h, h2]

theorem A072939_T_eq (a b : Nat) : A072939_T (a, b) = (b, A072939_step a b) := rfl

theorem A072939_it2 (a b : Nat) :
    A072939_it (a, b) 2 = (A072939_step a b, A072939_step b (A072939_step a b)) := rfl

theorem A072939_even_or_odd (j : Nat) : ∃ k, j = 2 * k ∨ j = 2 * k + 1 :=
  ⟨j / 2, by omega⟩

/-- c(k+1) in the entry's indexing. -/
def A072939_c (n k : Nat) : Nat := (A072939_it (1, n) k).1

def A072939_diverges (n : Nat) : Prop := ∀ M, ∃ K, ∀ k, K ≤ k → M ≤ A072939_c n k

theorem A072939_it_add (p : Nat × Nat) (j : Nat) : ∀ k,
    A072939_it p (j + k) = A072939_it (A072939_it p j) k
  | 0 => rfl
  | k + 1 => by
    show A072939_T (A072939_it p (j + k)) = A072939_T (A072939_it (A072939_it p j) k)
    rw [A072939_it_add p j k]

theorem A072939_it_succ_first (p : Nat × Nat) (k : Nat) :
    A072939_it p (k + 1) = A072939_it (A072939_T p) k := by
  rw [Nat.add_comm, A072939_it_add]; rfl

/-- Two steps from (b+m, b), m odd. -/
theorem A072939_down2 (b m : Nat) (hm : m % 2 = 1) :
    A072939_it (b + m, b) 2 = (b + 2 * m, b + m) := by
  rw [A072939_it2, A072939_step_dn (b + m) b (by omega) (by omega),
    A072939_step_same b (2 * (b + m) - b) (by omega)]
  ext <;> simp <;> omega

theorem A072939_down_iter (b m : Nat) (hm : m % 2 = 1) : ∀ k,
    A072939_it (b + m, b) (2 * k) = (b + (k + 1) * m, b + k * m)
  | 0 => by simp [A072939_it]
  | k + 1 => by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, A072939_it_add, A072939_down_iter b m hm k]
    have := A072939_down2 (b + k * m) m hm
    rw [show b + k * m + m = b + (k + 1) * m by rw [Nat.succ_mul]; omega] at this
    rw [this]
    ext <;> simp [Nat.succ_mul] <;> omega

theorem A072939_down_grow (b m : Nat) (hm : m % 2 = 1) (j : Nat) :
    j / 2 ≤ (A072939_it (b + m, b) j).1 := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨k, rfl | rfl⟩ := A072939_even_or_odd j
  · rw [A072939_down_iter b m hm k]
    have : k + 1 ≤ (k + 1) * m := Nat.le_mul_of_pos_right _ hm1
    simp; omega
  · show (2 * k + 1) / 2 ≤ (A072939_T (A072939_it (b + m, b) (2 * k))).1
    rw [A072939_down_iter b m hm k]
    have : k ≤ k * m := Nat.le_mul_of_pos_right _ hm1
    simp [A072939_T]; omega

theorem A072939_div_of_down (n K0 b m : Nat) (hm : m % 2 = 1)
    (h : A072939_it (1, n) K0 = (b + m, b)) : A072939_diverges n := by
  intro M
  refine ⟨K0 + 2 * M, fun k hk => ?_⟩
  have hk' : k = K0 + (k - K0) := by omega
  unfold A072939_c
  rw [hk', A072939_it_add, h]
  have := A072939_down_grow b m hm (k - K0)
  omega

theorem A072939_fix_it : ∀ k, A072939_it (1, 1) k = (1, 1)
  | 0 => rfl
  | k + 1 => by
    show A072939_T (A072939_it (1, 1) k) = (1, 1)
    rw [A072939_fix_it k]; rfl

theorem A072939_not_div_of_fix (n K0 : Nat) (h : A072939_it (1, n) K0 = (1, 1)) :
    ¬ A072939_diverges n := by
  intro hd
  obtain ⟨K, hK⟩ := hd 2
  have := hK (K + K0) (by omega)
  unfold A072939_c at this
  rw [Nat.add_comm, A072939_it_add, h, A072939_fix_it] at this
  simp at this

/-- up(x, 1) reaches (1, 1). -/
theorem A072939_gap1 : ∀ x, ∃ k, A072939_it (x, x + 1) k = (1, 1)
  | 0 => ⟨1, by decide⟩
  | x + 1 => by
    obtain ⟨k, hk⟩ := A072939_gap1 x
    refine ⟨2 + k, ?_⟩
    rw [A072939_it_add]
    have : A072939_it (x + 1, x + 1 + 1) 2 = (x, x + 1) := by
      by_cases h2 : 2 * (x + 1) ≤ x + 1 + 1
      · have hx : x = 0 := by omega
        subst hx; decide
      · rw [A072939_it2, A072939_step_dn (x + 1) (x + 1 + 1) (by omega) h2,
          A072939_step_same (x + 1 + 1) (2 * (x + 1) - (x + 1 + 1)) (by omega)]
        ext <;> simp <;> omega
    rw [this, hk]

/-- up(1 + c u, u), u odd, reaches (1, 1). -/
theorem A072939_asc (u : Nat) (hu : u % 2 = 1) : ∀ c,
    ∃ k, A072939_it (1 + c * u, 1 + c * u + u) k = (1, 1)
  | 0 => by
    obtain ⟨k, hk⟩ := A072939_gap1 (u - 1)
    refine ⟨2 + k, ?_⟩
    rw [A072939_it_add]
    have : A072939_it (1 + 0 * u, 1 + 0 * u + u) 2 = (u - 1, u - 1 + 1) := by
      simp only [Nat.zero_mul, Nat.add_zero]
      rw [A072939_it2, A072939_step_up 1 (1 + u) (by omega) (by omega),
        A072939_step_same (1 + u) (1 + u - 2 * 1) (by omega)]
      ext <;> simp <;> omega
    rw [this, hk]
  | c + 1 => by
    obtain ⟨k, hk⟩ := A072939_asc u hu c
    refine ⟨2 + k, ?_⟩
    rw [A072939_it_add]
    have : A072939_it (1 + (c + 1) * u, 1 + (c + 1) * u + u) 2 = (1 + c * u, 1 + c * u + u) := by
      rw [Nat.succ_mul, A072939_it2, A072939_step_dn (1 + (c * u + u)) (1 + (c * u + u) + u)
        (by omega) (by omega), A072939_step_same (1 + (c * u + u) + u)
        (2 * (1 + (c * u + u)) - (1 + (c * u + u) + u)) (by omega)]
      ext <;> simp <;> omega
    rw [this, hk]

/-- up(a, E) for o = true, down(a, E) for o = false. -/
def A072939_pr : Bool → Nat → Nat → Nat × Nat
  | true, a, E => (a, a + E)
  | false, a, E => (a + E, a)

theorem A072939_halve_step (o : Bool) (a D : Nat) :
    A072939_T (A072939_pr o a (2 * D)) =
      A072939_pr (!o) (a + (if o then D else 0)) D := by
  cases o
  · simp only [A072939_pr]
    rw [A072939_T_eq, A072939_step_same _ _ (by omega)]
    ext <;> simp <;> omega
  · simp only [A072939_pr]
    rw [A072939_T_eq, A072939_step_same _ _ (by omega)]
    ext <;> simp <;> omega

theorem A072939_halve (u : Nat) : ∀ v (o : Bool) a, ∃ c,
    A072939_it (A072939_pr o a (2 ^ v * u)) v =
      A072939_pr (if v % 2 = 0 then o else !o) (a + c * u) u
  | 0, o, a => ⟨0, by simp [A072939_it]⟩
  | v + 1, o, a => by
    rw [A072939_it_succ_first, Nat.pow_succ, Nat.mul_comm (2 ^ v) 2, Nat.mul_assoc,
      A072939_halve_step]
    obtain ⟨c, hc⟩ := A072939_halve u v (!o) (a + (if o then 2 ^ v * u else 0))
    refine ⟨c + (if o then 2 ^ v else 0), ?_⟩
    rw [hc]
    have e : a + (if o then 2 ^ v * u else 0) + c * u = a + (c + (if o then 2 ^ v else 0)) * u := by
      cases o <;> simp [Nat.add_mul] <;> omega
    rw [e]
    congr 1
    cases o <;> rcases Nat.mod_two_eq_zero_or_one v with h | h <;>
      simp [h, show (v + 1) % 2 = 1 - v % 2 by omega]

theorem A072939_decomp : ∀ N, 1 ≤ N → ∃ v u, N = 2 ^ v * (2 * u + 1)
  | N, h => by
    rcases Nat.mod_two_eq_zero_or_one N with he | ho
    · have : N / 2 < N := by omega
      obtain ⟨v, u, hvu⟩ := A072939_decomp (N / 2) (by omega)
      refine ⟨v + 1, u, ?_⟩
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ v) 2, Nat.mul_assoc, ← hvu]; omega
    · exact ⟨0, N / 2, by simp; omega⟩

theorem A072939_main (n : Nat) (hn : 1 ≤ n) :
    A072939_diverges n ↔ ∃ j u, n = 2 ^ (2 * j + 1) * (2 * u + 1) + 1 := by
  constructor
  · intro hd
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · exact absurd hd (A072939_not_div_of_fix n 0 (by simp [A072939_it]; omega))
    · obtain ⟨v, u, hvu⟩ := A072939_decomp (n - 1) (by omega)
      obtain ⟨j, rfl | rfl⟩ := A072939_even_or_odd v
      · exfalso
        obtain ⟨c, hc⟩ := A072939_halve (2 * u + 1) (2 * j) true 1
        have e : A072939_pr true 1 (2 ^ (2 * j) * (2 * u + 1)) = (1, n) := by
          simp [A072939_pr]; omega
        rw [e] at hc
        simp [A072939_pr] at hc
        obtain ⟨k, hk⟩ := A072939_asc (2 * u + 1) (by omega) c
        refine A072939_not_div_of_fix n (2 * j + k) ?_ hd
        rw [A072939_it_add, hc, hk]
      · exact ⟨j, u, by omega⟩
  · rintro ⟨j, u, rfl⟩
    obtain ⟨c, hc⟩ := A072939_halve (2 * u + 1) (2 * j + 1) true 1
    have e : A072939_pr true 1 (2 ^ (2 * j + 1) * (2 * u + 1)) =
        (1, 2 ^ (2 * j + 1) * (2 * u + 1) + 1) := by
      simp [A072939_pr]; omega
    rw [e] at hc
    have h2 : (2 * j + 1) % 2 = 1 := by omega
    simp [h2, A072939_pr] at hc
    exact A072939_div_of_down _ _ _ _ (by omega) hc

/-- The first listed terms: for 1 ≤ n ≤ 60, `A072939_c n 200 > 25` exactly at the data terms. -/
theorem A072939_data :
    ((List.range 61).filter (fun n => 1 ≤ n && 25 < A072939_c n 200)) =
      [3, 7, 9, 11, 15, 19, 23, 25, 27, 31, 33, 35, 39, 41, 43, 47, 51, 55, 57, 59] := by
  decide +kernel
