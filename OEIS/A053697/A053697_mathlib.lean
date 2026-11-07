/-
OEIS A053697: a(n+1) = a(n) + a^(n), addition in base 11, where a^(n) replaces
each base-11 digit of a(n) by its inverse mod 11 and deletes zero digits.
Conjecture (entry): from every start the orbit eventually runs through
  [1][4^a][3][(84)^b] -> ... -> [1][4^a][3][(84)^(b+1)]   (six steps), or
  [1][5^a][4][(84)^b] -> ... -> [1][5^a][4][(84)^(b+1)]   (six steps).

Checked here (all a, b):
* `famI_cycle`: step^6 of [1][4^a][3][(84)^b] is [1][4^a][3][(84)^(b+1)], with the
  five intermediate forms 2 7^a (84)^b 7, 9 5^a 4 (84)^b, 1 4^a 3 (84)^b 7,
  2 7^a (84)^(b+1), 9 5^a 4 (84)^b 7 (`famI_1` ... `famI_6`).
* `famII_cycle`: the same for [1][5^(c+1)][4][(84)^b] (a = c + 1 >= 1), via
  3 4^c 3 (84)^b 7, 7^(c+1) (84)^(b+1), 1 5^(c+1) 4 (84)^b 7,
  3 4^c 3 (84)^(b+1), 7^(c+1) (84)^(b+1) 7. (For a = 0, [1][4][(84)^b] steps to
  2 (84)^b 7, the second form of family I with a = 0; not separately stated here.)
* `A053697_one_orbit`: from a(1) = 1, a(10 + 6k) = [1][3][(84)^(k+1)] for all k
  (the entry's example is family I with a = 0).
Digit lists are least-significant-digit first (Mathlib `Nat.digits` convention).
Not checked here: that every start reaches a family (open; certificate/scan.py
checks all starts below 11^7).
-/
import Mathlib

open Nat List


/-- Inverse of a base-11 digit mod 11 (0 is mapped to 0 but is deleted first). -/
def inv11 (d : ℕ) : ℕ := (d ^ 9) % 11

/-- a^: delete zero digits, invert the others. -/
def hat (L : List ℕ) : List ℕ := (L.filter (fun d => d ≠ 0)).map inv11

/-- One step of A053697. -/
def step (n : ℕ) : ℕ := n + ofDigits 11 (hat (digits 11 n))

/-- (84)^b written least significant digit first: [4,8,4,8,...]. -/
def P : ℕ → List ℕ
  | 0 => []
  | b + 1 => 4 :: 8 :: P b

/-- its digit inverse, (73)^b: [3,7,3,7,...]. -/
def Q : ℕ → List ℕ
  | 0 => []
  | b + 1 => 3 :: 7 :: Q b

lemma hat_append (L M : List ℕ) : hat (L ++ M) = hat L ++ hat M := by
  simp [hat, List.filter_append]

lemma hat_rep (n d : ℕ) (hd : d ≠ 0) : hat (replicate n d) = replicate n (inv11 d) := by
  induction n with
  | zero => simp [hat]
  | succ n ih =>
    simp only [hat, replicate_succ, List.filter_cons, hd, decide_true, ↓reduceIte,
      List.map_cons, ne_eq, not_false_eq_true] at ih ⊢
    rw [ih]

lemma hat_P (b : ℕ) : hat (P b) = Q b := by
  induction b with
  | zero => simp [hat, P, Q]
  | succ b ih =>
    simp only [hat] at ih ⊢
    simp [P, Q, inv11]
    simpa using ih

lemma hat_single (d : ℕ) (hd : d ≠ 0) : hat [d] = [inv11 d] := by simp [hat, hd]

lemma P_len (b : ℕ) : (P b).length = 2 * b := by
  induction b with
  | zero => simp [P]
  | succ b ih => simp [P, ih]; ring

lemma Q_len (b : ℕ) : (Q b).length = 2 * b := by
  induction b with
  | zero => simp [Q]
  | succ b ih => simp [Q, ih]; ring

lemma P_mem (b : ℕ) : ∀ x ∈ P b, x = 4 ∨ x = 8 := by
  induction b with
  | zero => simp [P]
  | succ b ih => intro x hx; simp [P] at hx; rcases hx with h | h | h <;> simp_all

/-- values, cast to ℚ -/
lemma val_rep (n d : ℕ) : (ofDigits 11 (replicate n d) : ℚ) = d * ((11:ℚ) ^ n - 1) / 10 := by
  induction n with
  | zero => simp [Nat.ofDigits]
  | succ n ih =>
    rw [replicate_succ]
    simp only [Nat.ofDigits, ih]
    ring

lemma val_P (b : ℕ) : (ofDigits 11 (P b) : ℚ) = 92 * ((11:ℚ) ^ (2 * b) - 1) / 120 := by
  induction b with
  | zero => simp [P, Nat.ofDigits]
  | succ b ih =>
    simp only [P, Nat.ofDigits, ih]
    push_cast
    ring

lemma val_Q (b : ℕ) : (ofDigits 11 (Q b) : ℚ) = 80 * ((11:ℚ) ^ (2 * b) - 1) / 120 := by
  induction b with
  | zero => simp [Q, Nat.ofDigits]
  | succ b ih =>
    simp only [Q, Nat.ofDigits, ih]
    push_cast
    ring

lemma digits_of (L : List ℕ) (h1 : ∀ x ∈ L, x < 11) (h2 : ∀ h : L ≠ [], L.getLast h ≠ 0) :
    digits 11 (ofDigits 11 L) = L := digits_ofDigits 11 (by norm_num) L h1 h2

lemma P_lt (b : ℕ) : ∀ x ∈ P b, x < 11 := fun x hx => by
  rcases P_mem b x hx with h | h <;> omega

@[simp] lemma inv11_1 : inv11 1 = 1 := by decide
@[simp] lemma inv11_2 : inv11 2 = 6 := by decide
@[simp] lemma inv11_3 : inv11 3 = 4 := by decide
@[simp] lemma inv11_4 : inv11 4 = 3 := by decide
@[simp] lemma inv11_5 : inv11 5 = 9 := by decide
@[simp] lemma inv11_7 : inv11 7 = 8 := by decide
@[simp] lemma inv11_8 : inv11 8 = 7 := by decide
@[simp] lemma inv11_9 : inv11 9 = 5 := by decide

/-- Generic step lemma: if the value identity holds over ℚ, the step is as claimed. -/
lemma step_eq (L M : List ℕ) (h1 : ∀ x ∈ L, x < 11) (h2 : ∀ h : L ≠ [], L.getLast h ≠ 0)
    (hv : ((Nat.ofDigits 11 L : ℕ) : ℚ) + ((Nat.ofDigits 11 (hat L) : ℕ) : ℚ)
      = ((Nat.ofDigits 11 M : ℕ) : ℚ)) :
    step (ofDigits 11 L) = ofDigits 11 M := by
  unfold step
  rw [digits_of L h1 h2]
  exact_mod_cast hv

def X0 (a b : ℕ) : List ℕ := P b ++ [3] ++ replicate a 4 ++ [1]
def X1 (a b : ℕ) : List ℕ := [7] ++ P b ++ replicate a 7 ++ [2]
def X2 (a b : ℕ) : List ℕ := P b ++ [4] ++ replicate a 5 ++ [9]
def X3 (a b : ℕ) : List ℕ := [7] ++ P b ++ [3] ++ replicate a 4 ++ [1]
def X4 (a b : ℕ) : List ℕ := P (b + 1) ++ replicate a 7 ++ [2]
def X5 (a b : ℕ) : List ℕ := [7] ++ P b ++ [4] ++ replicate a 5 ++ [9]
def Y0 (c b : ℕ) : List ℕ := P b ++ [4] ++ replicate (c + 1) 5 ++ [1]
def Y1 (c b : ℕ) : List ℕ := [7] ++ P b ++ [3] ++ replicate c 4 ++ [3]
def Y2 (c b : ℕ) : List ℕ := P (b + 1) ++ replicate c 7 ++ [7]
def Y3 (c b : ℕ) : List ℕ := [7] ++ P b ++ [4] ++ replicate (c + 1) 5 ++ [1]
def Y4 (c b : ℕ) : List ℕ := P (b + 1) ++ [3] ++ replicate c 4 ++ [3]
def Y5 (c b : ℕ) : List ℕ := [7] ++ P (b + 1) ++ replicate c 7 ++ [7]

theorem famI_1 (a b : ℕ) : step (ofDigits 11 (X0 a b)) = ofDigits 11 (X1 a b) := by
  apply step_eq
  · have h0 := P_lt b
    have h1 := P_lt (b + 1)
    intro x hx
    simp only [X0, List.mem_append, List.mem_replicate,
      List.mem_singleton] at hx
    aesop
  · intro h
    simp [X0]
  · simp only [X0, X1, hat_append, hat_P,
      hat_rep _ _ (by norm_num : (4:ℕ) ≠ 0),
      hat_single _ (by norm_num : (1:ℕ) ≠ 0),
      hat_single _ (by norm_num : (3:ℕ) ≠ 0),
      inv11_1, inv11_3, inv11_4,
      Nat.ofDigits_append, List.length_append, List.length_replicate, P_len, Q_len,
      List.length_singleton]
    push_cast
    simp only [val_rep, val_P, val_Q, Nat.ofDigits]
    push_cast
    ring

theorem famI_2 (a b : ℕ) : step (ofDigits 11 (X1 a b)) = ofDigits 11 (X2 a b) := by
  apply step_eq
  · have h0 := P_lt b
    have h1 := P_lt (b + 1)
    intro x hx
    simp only [X1, List.mem_append, List.mem_replicate,
      List.mem_singleton] at hx
    aesop
  · intro h
    simp [X1]
  · simp only [X1, X2, hat_append, hat_P,
      hat_rep _ _ (by norm_num : (7:ℕ) ≠ 0),
      hat_single _ (by norm_num : (2:ℕ) ≠ 0),
      hat_single _ (by norm_num : (7:ℕ) ≠ 0),
      inv11_2, inv11_7,
      Nat.ofDigits_append, List.length_append, List.length_replicate, P_len, Q_len,
      List.length_singleton]
    push_cast
    simp only [val_rep, val_P, val_Q, Nat.ofDigits]
    push_cast
    ring

theorem famI_3 (a b : ℕ) : step (ofDigits 11 (X2 a b)) = ofDigits 11 (X3 a b) := by
  apply step_eq
  · have h0 := P_lt b
    have h1 := P_lt (b + 1)
    intro x hx
    simp only [X2, List.mem_append, List.mem_replicate,
      List.mem_singleton] at hx
    aesop
  · intro h
    simp [X2]
  · simp only [X2, X3, hat_append, hat_P,
      hat_rep _ _ (by norm_num : (5:ℕ) ≠ 0),
      hat_single _ (by norm_num : (4:ℕ) ≠ 0),
      hat_single _ (by norm_num : (9:ℕ) ≠ 0),
      inv11_4, inv11_5, inv11_9,
      Nat.ofDigits_append, List.length_append, List.length_replicate, P_len, Q_len,
      List.length_singleton]
    push_cast
    simp only [val_rep, val_P, val_Q, Nat.ofDigits]
    push_cast
    ring

theorem famI_4 (a b : ℕ) : step (ofDigits 11 (X3 a b)) = ofDigits 11 (X4 a b) := by
  apply step_eq
  · have h0 := P_lt b
    have h1 := P_lt (b + 1)
    intro x hx
    simp only [X3, List.mem_append, List.mem_replicate,
      List.mem_singleton] at hx
    aesop
  · intro h
    simp [X3]
  · simp only [X3, X4, hat_append, hat_P,
      hat_rep _ _ (by norm_num : (4:ℕ) ≠ 0),
      hat_single _ (by norm_num : (1:ℕ) ≠ 0),
      hat_single _ (by norm_num : (3:ℕ) ≠ 0),
      hat_single _ (by norm_num : (7:ℕ) ≠ 0),
      inv11_1, inv11_3, inv11_4, inv11_7,
      Nat.ofDigits_append, List.length_append, List.length_replicate, P_len, Q_len,
      List.length_singleton]
    push_cast
    simp only [val_rep, val_P, val_Q, Nat.ofDigits]
    push_cast
    ring

theorem famI_5 (a b : ℕ) : step (ofDigits 11 (X4 a b)) = ofDigits 11 (X5 a b) := by
  apply step_eq
  · have h0 := P_lt b
    have h1 := P_lt (b + 1)
    intro x hx
    simp only [X4, List.mem_append, List.mem_replicate,
      List.mem_singleton] at hx
    aesop
  · intro h
    simp [X4]
  · simp only [X4, X5, hat_append, hat_P,
      hat_rep _ _ (by norm_num : (7:ℕ) ≠ 0),
      hat_single _ (by norm_num : (2:ℕ) ≠ 0),

      inv11_2, inv11_7,
      Nat.ofDigits_append, List.length_append, List.length_replicate, P_len, Q_len,
      List.length_singleton]
    push_cast
    simp only [val_rep, val_P, val_Q, Nat.ofDigits]
    push_cast
    ring

theorem famI_6 (a b : ℕ) : step (ofDigits 11 (X5 a b)) = ofDigits 11 (X0 a (b + 1)) := by
  apply step_eq
  · have h0 := P_lt b
    have h1 := P_lt (b + 1)
    intro x hx
    simp only [X5, List.mem_append, List.mem_replicate,
      List.mem_singleton] at hx
    aesop
  · intro h
    simp [X5]
  · simp only [X0, X5, hat_append, hat_P,
      hat_rep _ _ (by norm_num : (5:ℕ) ≠ 0),
      hat_single _ (by norm_num : (4:ℕ) ≠ 0),
      hat_single _ (by norm_num : (7:ℕ) ≠ 0), hat_single _ (by norm_num : (9:ℕ) ≠ 0),
      inv11_4, inv11_5, inv11_7, inv11_9,
      Nat.ofDigits_append, List.length_append, List.length_replicate, P_len, Q_len,
      List.length_singleton]
    push_cast
    simp only [val_rep, val_P, val_Q, Nat.ofDigits]
    push_cast
    ring

theorem famII_1 (c b : ℕ) : step (ofDigits 11 (Y0 c b)) = ofDigits 11 (Y1 c b) := by
  apply step_eq
  · have h0 := P_lt b
    have h1 := P_lt (b + 1)
    intro x hx
    simp only [Y0, List.mem_append, List.mem_replicate,
      List.mem_singleton] at hx
    aesop
  · intro h
    simp [Y0]
  · simp only [Y0, Y1, hat_append, hat_P,
      hat_rep _ _ (by norm_num : (5:ℕ) ≠ 0),
      hat_single _ (by norm_num : (1:ℕ) ≠ 0),
      hat_single _ (by norm_num : (4:ℕ) ≠ 0),
      inv11_1, inv11_4, inv11_5,
      Nat.ofDigits_append, List.length_append, List.length_replicate, P_len, Q_len,
      List.length_singleton]
    push_cast
    simp only [val_rep, val_P, val_Q, Nat.ofDigits]
    push_cast
    ring

theorem famII_2 (c b : ℕ) : step (ofDigits 11 (Y1 c b)) = ofDigits 11 (Y2 c b) := by
  apply step_eq
  · have h0 := P_lt b
    have h1 := P_lt (b + 1)
    intro x hx
    simp only [Y1, List.mem_append, List.mem_replicate,
      List.mem_singleton] at hx
    aesop
  · intro h
    simp [Y1]
  · simp only [Y1, Y2, hat_append, hat_P,
      hat_rep _ _ (by norm_num : (4:ℕ) ≠ 0),

      hat_single _ (by norm_num : (3:ℕ) ≠ 0),
      hat_single _ (by norm_num : (7:ℕ) ≠ 0),
      inv11_3, inv11_4, inv11_7,
      Nat.ofDigits_append, List.length_append, List.length_replicate, P_len, Q_len,
      List.length_singleton]
    push_cast
    simp only [val_rep, val_P, val_Q, Nat.ofDigits]
    push_cast
    ring

theorem famII_3 (c b : ℕ) : step (ofDigits 11 (Y2 c b)) = ofDigits 11 (Y3 c b) := by
  apply step_eq
  · have h0 := P_lt b
    have h1 := P_lt (b + 1)
    intro x hx
    simp only [Y2, List.mem_append, List.mem_replicate,
      List.mem_singleton] at hx
    aesop
  · intro h
    simp [Y2]
  · simp only [Y2, Y3, hat_append, hat_P,
      hat_rep _ _ (by norm_num : (7:ℕ) ≠ 0),

      hat_single _ (by norm_num : (7:ℕ) ≠ 0),
      inv11_7,
      Nat.ofDigits_append, List.length_append, List.length_replicate, P_len, Q_len,
      List.length_singleton]
    push_cast
    simp only [val_rep, val_P, val_Q, Nat.ofDigits]
    push_cast
    ring

theorem famII_4 (c b : ℕ) : step (ofDigits 11 (Y3 c b)) = ofDigits 11 (Y4 c b) := by
  apply step_eq
  · have h0 := P_lt b
    have h1 := P_lt (b + 1)
    intro x hx
    simp only [Y3, List.mem_append, List.mem_replicate,
      List.mem_singleton] at hx
    aesop
  · intro h
    simp [Y3]
  · simp only [Y3, Y4, hat_append, hat_P,
      hat_rep _ _ (by norm_num : (5:ℕ) ≠ 0),
      hat_single _ (by norm_num : (1:ℕ) ≠ 0),
      hat_single _ (by norm_num : (4:ℕ) ≠ 0),
      hat_single _ (by norm_num : (7:ℕ) ≠ 0),
      inv11_1, inv11_4, inv11_5, inv11_7,
      Nat.ofDigits_append, List.length_append, List.length_replicate, P_len, Q_len,
      List.length_singleton]
    push_cast
    simp only [val_rep, val_P, val_Q, Nat.ofDigits]
    push_cast
    ring

theorem famII_5 (c b : ℕ) : step (ofDigits 11 (Y4 c b)) = ofDigits 11 (Y5 c b) := by
  apply step_eq
  · have h0 := P_lt b
    have h1 := P_lt (b + 1)
    intro x hx
    simp only [Y4, List.mem_append, List.mem_replicate,
      List.mem_singleton] at hx
    aesop
  · intro h
    simp [Y4]
  · simp only [Y4, Y5, hat_append, hat_P,
      hat_rep _ _ (by norm_num : (4:ℕ) ≠ 0),

      hat_single _ (by norm_num : (3:ℕ) ≠ 0),
      inv11_3, inv11_4,
      Nat.ofDigits_append, List.length_append, List.length_replicate, P_len, Q_len,
      List.length_singleton]
    push_cast
    simp only [val_rep, val_P, val_Q, Nat.ofDigits]
    push_cast
    ring

theorem famII_6 (c b : ℕ) : step (ofDigits 11 (Y5 c b)) = ofDigits 11 (Y0 c (b + 1)) := by
  apply step_eq
  · have h0 := P_lt b
    have h1 := P_lt (b + 1)
    intro x hx
    simp only [Y5, List.mem_append, List.mem_replicate,
      List.mem_singleton] at hx
    aesop
  · intro h
    simp [Y5]
  · simp only [Y0, Y5, hat_append, hat_P,
      hat_rep _ _ (by norm_num : (7:ℕ) ≠ 0),

      hat_single _ (by norm_num : (7:ℕ) ≠ 0),
      inv11_7,
      Nat.ofDigits_append, List.length_append, List.length_replicate, P_len, Q_len,
      List.length_singleton]
    push_cast
    simp only [val_rep, val_P, val_Q, Nat.ofDigits]
    push_cast
    ring

theorem famI_cycle (a b : ℕ) : step^[6] (ofDigits 11 (X0 a b)) = ofDigits 11 (X0 a (b + 1)) := by
  simp only [Function.iterate_succ, Function.comp]
  rw [famI_1, famI_2, famI_3, famI_4, famI_5, famI_6]
  rfl

theorem famII_cycle (c b : ℕ) : step^[6] (ofDigits 11 (Y0 c b)) = ofDigits 11 (Y0 c (b + 1)) := by
  simp only [Function.iterate_succ, Function.comp]
  rw [famII_1, famII_2, famII_3, famII_4, famII_5, famII_6]
  rfl

theorem start_four : step^[4] 1 = ofDigits 11 (X1 0 0) := by
  norm_num [Function.iterate_succ, step, hat, inv11, X1, P, Nat.ofDigits]

/-- The entry's example a(1) = 1: a(10 + 6k) = [1][3][(84)^(k+1)] (family I, a = 0). -/
theorem A053697_one_orbit (k : ℕ) : step^[9 + 6 * k] 1 = ofDigits 11 (X0 0 (k + 1)) := by
  induction k with
  | zero =>
    rw [show 9 + 6 * 0 = 5 + 4 by rfl, Function.iterate_add_apply, start_four]
    simp only [Function.iterate_succ, Function.comp]
    rw [famI_2, famI_3, famI_4, famI_5, famI_6]
    rfl
  | succ k ih =>
    rw [show 9 + 6 * (k + 1) = 6 + (9 + 6 * k) by ring, Function.iterate_add_apply, ih, famI_cycle]

