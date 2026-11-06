/-
Guy, Unsolved Problems in Number Theory (3rd ed.), D24 (Erdős): for a primitive
A = {a_1 < ... < a_k} ⊆ [1, x] (no element divides another) let f(A; n) be the
number of a_i ≤ n. Is max_A Σ_{n=1}^{x} f(A; n) = x²/6 + O(x)?

Answer: no. For x = 18N the primitive set
  A_N = {odd a : 6N < a < 18N} ∪ {a ≡ 2 (mod 4) : 4N < a < 12N}
has Σ_{n ≤ x} f(A_N; n) = 56N² + 8N = (14/81)x² + 8N > x²/6 + Cx for N large.

Checked here (core Lean, all N, no decide): A_N lies in [1, 18N] and is primitive
(`AN_primitive`); S(A, x) = Σ_{a ∈ A} (x + 1 − a) (`S_eq_W`); S(A_N, 18N) = 56N² + 8N
(`S_AN`); main theorem `D24_3_main`: for every C and x0 there are x ≥ x0 and a
primitive A ⊆ [1, x] with x² + C·x < 6·Σ_{n=1}^{x} f(A; n).
Not checked here: nothing beyond reading f(A; n) as #{a ∈ A : a ≤ n}
(Guy writes a_i < n; that changes the sum by |A| ≤ x, absorbed by C).
-/

/-- f(A; n): number of elements of A that are ≤ n. -/
def f (A : List Nat) (n : Nat) : Nat := (A.filter (fun a => decide (a ≤ n))).length

/-- S(A, x) = Σ_{n=1}^{x} f(A; n). -/
def S (A : List Nat) : Nat → Nat
  | 0 => 0
  | x + 1 => S A x + f A (x + 1)

/-- Σ_{a ∈ A} (x + 1 − a). -/
def W (A : List Nat) (x : Nat) : Nat := (A.map (fun a => x + 1 - a)).sum

/-- A is primitive: no element divides a different one. -/
def Primitive (A : List Nat) : Prop := ∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b

theorem W_succ (A : List Nat) (x : Nat) (h : ∀ a ∈ A, 1 ≤ a) :
    W A (x + 1) = W A x + f A (x + 1) := by
  induction A with
  | nil => simp [W, f]
  | cons a t ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [W, f, List.map_cons, List.sum_cons, List.filter_cons] at ht ⊢
    by_cases hax : a ≤ x + 1
    · simp [hax]; omega
    · simp [hax]; omega

theorem S_eq_W (A : List Nat) (h : ∀ a ∈ A, 1 ≤ a) : ∀ x, S A x = W A x := by
  intro x
  induction x with
  | zero =>
    simp only [S, W]
    have : ∀ l : List Nat, (∀ a ∈ l, 1 ≤ a) → (l.map (fun a => 0 + 1 - a)).sum = 0 := by
      intro l hl
      induction l with
      | nil => rfl
      | cons a t ih =>
        simp only [List.map_cons, List.sum_cons]
        have := hl a (by simp)
        rw [ih (fun b hb => hl b (by simp [hb]))]; omega
    exact (this A h).symm
  | succ x ih => rw [S, ih, W_succ A x h]

def L0 (N : Nat) : List Nat := (List.range (6 * N)).map (fun i => 6 * N + 2 * i + 1)
def L1 (N : Nat) : List Nat := (List.range (2 * N)).map (fun i => 4 * N + 4 * i + 2)
def AN (N : Nat) : List Nat := L0 N ++ L1 N

theorem mem_AN (N b : Nat) (hb : b ∈ AN N) :
    (b % 2 = 1 ∧ 6 * N < b ∧ b < 18 * N) ∨ (b % 4 = 2 ∧ 4 * N < b ∧ b < 12 * N) := by
  simp only [AN, L0, L1, List.mem_append, List.mem_map, List.mem_range] at hb
  rcases hb with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · left; omega
  · right; omega

theorem AN_range (N : Nat) : ∀ a ∈ AN N, 1 ≤ a ∧ a ≤ 18 * N := by
  intro a ha; rcases mem_AN N a ha with h | h <;> omega

theorem AN_primitive (N : Nat) : Primitive (AN N) := by
  intro a ha b hb hab
  have ha' := mem_AN N a ha
  have hb' := mem_AN N b hb
  have h2b : a % 2 = 0 → b % 2 = 0 := fun h0 =>
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h0) hab)
  obtain ⟨k, rfl⟩ := hab
  rcases k with _ | _ | _ | k
  · omega
  · omega
  · omega
  · have : a * (k + 1 + 1 + 1) ≥ a * 3 := Nat.mul_le_mul_left _ (by omega)
    omega

theorem sum2 (c : Nat) : ∀ m, 2 * m ≤ c →
    ((List.range m).map (fun i => c - 2 * i)).sum + m * m = m * c + m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm
    rw [List.range_succ, List.map_append, List.sum_append]
    have := ih (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have e1 : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by grind
    have e2 : (m + 1) * c = m * c + c := by grind
    omega

theorem sum4 (c : Nat) : ∀ m, 4 * m ≤ c →
    ((List.range m).map (fun i => c - 4 * i)).sum + 2 * (m * m) = m * c + 2 * m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm
    rw [List.range_succ, List.map_append, List.sum_append]
    have := ih (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have e1 : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by grind
    have e2 : (m + 1) * c = m * c + c := by grind
    omega

theorem W_AN (N : Nat) : W (AN N) (18 * N) = 56 * (N * N) + 8 * N := by
  simp only [W, AN, L0, L1, List.map_append, List.sum_append, List.map_map]
  have h0 : ((List.range (6 * N)).map ((fun a => 18 * N + 1 - a) ∘ fun i => 6 * N + 2 * i + 1))
      = (List.range (6 * N)).map (fun i => 12 * N - 2 * i) := by
    apply List.map_congr_left; intro i hi; simp at hi; simp; omega
  have h1 : ((List.range (2 * N)).map ((fun a => 18 * N + 1 - a) ∘ fun i => 4 * N + 4 * i + 2))
      = (List.range (2 * N)).map (fun i => (14 * N - 1) - 4 * i) := by
    apply List.map_congr_left; intro i hi; simp at hi; simp; omega
  rw [h0, h1]
  have s0 := sum2 (12 * N) (6 * N) (by omega)
  have s1 := sum4 (14 * N - 1) (2 * N) (by omega)
  have e0 : 6 * N * (6 * N) = 36 * (N * N) := by grind
  have e1 : 6 * N * (12 * N) = 72 * (N * N) := by grind
  have e2 : 2 * N * (2 * N) = 4 * (N * N) := by grind
  have e3 : 2 * N * (14 * N - 1) + 2 * N = 28 * (N * N) := by
    rcases N with _ | N
    · simp
    · grind
  omega

theorem S_AN (N : Nat) : S (AN N) (18 * N) = 56 * (N * N) + 8 * N := by
  rw [S_eq_W _ (fun a ha => (AN_range N a ha).1), W_AN]

/-- Main: the bound x²/6 + O(x) fails. For every C and x0 there are x ≥ x0 and a
primitive A ⊆ [1, x] with 6·Σ_{n=1}^{x} f(A; n) > x² + C·x. -/
theorem D24_3_main (C x0 : Nat) : ∃ x A, x0 ≤ x ∧ Primitive A ∧ (∀ a ∈ A, 1 ≤ a ∧ a ≤ x) ∧
    x * x + C * x < 6 * S A x := by
  refine ⟨18 * (2 * C + x0 + 1), AN (2 * C + x0 + 1), by omega, AN_primitive _, AN_range _, ?_⟩
  rw [S_AN]
  generalize hN : 2 * C + x0 + 1 = N
  have e0 : 18 * N * (18 * N) = 324 * (N * N) := by grind
  have e1 : C * (18 * N) = 18 * (C * N) := by grind
  have e2 : N * N = 2 * (C * N) + x0 * N + N := by subst hN; grind
  omega
