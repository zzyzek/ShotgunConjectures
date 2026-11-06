/-
OEIS A082981: start with S(0) = {1,1}; S(k) = I(S(k-1)), where I inserts
a(i)+a(i+1) between a(i) and a(i+1) whenever 4a(i+1) <= 5a(i). The sequence is
the limit of S(k). Conjectures (1)-(6) of the entry identify the sections
a(2n+1), a(4n+1), a(4n+2), a(4n+2)/2, a(4n+4), a(4n+4)/4 with A077442,
A038761, A077444, A002315, A005319, A001109.

Definitions.
* `ins`: the operation I on lists; `S k = ins^[k] [1, 1]`.
* `a n` (n >= 1): the limit, given by the block rule below; `A082981_limit`
  proves that position n-1 of S(k) equals `a n` for all large k.
* `A038761`, `A002315`, `A005319`, `A001109`: the recurrences of those
  entries (6x(n+1) - x(n) with their initial terms), over ℤ.
* `A077442 n = Nat.nth (fun x => IsSquare (2x^2 + 7)) n` (offset 0) and
  `A077444 n = Nat.nth (fun k => 2 ∣ k^2+4 ∧ IsSquare ((k^2+4)/2)) (n-1)`
  (offset 1), the definitions of those entries.

Main theorems.
* `A082981_limit`: for n >= 1, (S k)[n-1] = a n for all large k.
* `a_block`: a(4j+t) = 4c(j) + t d(j) for t <= 3, where (c,d)(0) = (0,1),
  (c,d)(j+1) = (c+d, 4c+5d).
* `conj1` .. `conj6`: the six conjectures.

Route. Insertion acts on each adjacent pair separately (`iter_split`), so
F k x y = ins^[k] [x,y] satisfies F (k+1) x y = F k x (x+y) ++ tail (F k (x+y) y)
when 4y <= 5x and F k x y = [x,y] otherwise. Following the leftmost live pair
gives the stable prefix (`PF_tv`). The sections satisfy x(n+2) = 6x(n+1) - x(n)
(`c_rec`, `d_rec`); the Pell-type sets are enumerated by descent
(`sol1_complete`, `sol3_complete`) with the invariant d^2 - 4cd - 4c^2 = 1.

Not checked in this file: agreement with the OEIS data terms
(certificate/check.py).
-/
import Mathlib

namespace A082981

open Function

/-! ### The insertion process -/

/-- The operation I: insert `a + b` between adjacent `a, b` when `4b ≤ 5a`. -/
def ins : List ℕ → List ℕ
  | [] => []
  | [a] => [a]
  | a :: b :: t => if 4 * b ≤ 5 * a then a :: (a + b) :: ins (b :: t) else a :: ins (b :: t)

/-- S(k). -/
def S (k : ℕ) : List ℕ := ins^[k] [1, 1]

lemma ins_cc (a b : ℕ) (t : List ℕ) : ins (a :: b :: t) =
    if 4 * b ≤ 5 * a then a :: (a + b) :: ins (b :: t) else a :: ins (b :: t) := by
  rw [ins]

lemma ins_one (a : ℕ) : ins [a] = [a] := by
  rw [ins]

lemma ins_head (a : ℕ) (r : List ℕ) : ∃ t, ins (a :: r) = a :: t := by
  cases r with
  | nil => exact ⟨[], ins_one a⟩
  | cons b t =>
    rw [ins_cc]
    split_ifs
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

lemma ins_last (l : List ℕ) (x : ℕ) : ∃ t, ins (l ++ [x]) = t ++ [x] := by
  induction l with
  | nil => exact ⟨[], ins_one x⟩
  | cons y l ih =>
    cases l with
    | nil =>
      show ∃ t, ins (y :: x :: []) = t ++ [x]
      rw [ins_cc, ins_one]
      split_ifs
      · exact ⟨[y, y + x], rfl⟩
      · exact ⟨[y], rfl⟩
    | cons z l =>
      obtain ⟨t, ht⟩ := ih
      show ∃ t', ins (y :: z :: (l ++ [x])) = t' ++ [x]
      have ht' : ins (z :: (l ++ [x])) = t ++ [x] := ht
      rw [ins_cc, ht']
      split_ifs
      · exact ⟨y :: (y + z) :: t, rfl⟩
      · exact ⟨y :: t, rfl⟩

lemma ins_split (l : List ℕ) (x : ℕ) (r : List ℕ) :
    ins (l ++ x :: r) = ins (l ++ [x]) ++ (ins (x :: r)).tail := by
  induction l with
  | nil =>
    obtain ⟨t, ht⟩ := ins_head x r
    show ins (x :: r) = ins [x] ++ (ins (x :: r)).tail
    rw [ht, ins_one]
    rfl
  | cons y l ih =>
    cases l with
    | nil =>
      obtain ⟨t, ht⟩ := ins_head x r
      show ins (y :: x :: r) = ins (y :: x :: []) ++ (ins (x :: r)).tail
      have e1 := ins_cc y x r
      have e2 := ins_cc y x []
      rw [e1, e2, ht, ins_one]
      split_ifs <;> rfl
    | cons z l =>
      show ins (y :: z :: (l ++ x :: r)) = ins (y :: z :: (l ++ [x])) ++ (ins (x :: r)).tail
      have ih' : ins (z :: (l ++ x :: r)) = ins (z :: (l ++ [x])) ++ (ins (x :: r)).tail := ih
      have e1 := ins_cc y z (l ++ x :: r)
      have e2 := ins_cc y z (l ++ [x])
      rw [e1, e2, ih']
      split_ifs <;> rfl

lemma iter_head (k a : ℕ) (r : List ℕ) : ∃ t, ins^[k] (a :: r) = a :: t := by
  induction k generalizing r with
  | zero => exact ⟨r, rfl⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ins_head a r
    rw [iterate_succ_apply, ht]
    exact ih t

lemma iter_split (k : ℕ) (l : List ℕ) (x : ℕ) (r : List ℕ) :
    ins^[k] (l ++ x :: r) = ins^[k] (l ++ [x]) ++ (ins^[k] (x :: r)).tail := by
  induction k generalizing l r with
  | zero => simp
  | succ k ih =>
    obtain ⟨t1, h1⟩ := ins_last l x
    obtain ⟨t2, h2⟩ := ins_head x r
    rw [iterate_succ_apply, iterate_succ_apply, iterate_succ_apply, ins_split, h1, h2]
    rw [show t1 ++ [x] ++ (x :: t2).tail = t1 ++ x :: t2 by simp]
    exact ih t1 t2

/-- The list grown from the pair `[x, y]` after `k` steps. -/
def F (k x y : ℕ) : List ℕ := ins^[k] [x, y]

lemma F_dead {x y : ℕ} (h : ¬ 4 * y ≤ 5 * x) (k : ℕ) : F k x y = [x, y] := by
  unfold F
  apply iterate_fixed
  rw [ins_cc, ite_eq_right_of_eq_false _ _ (eq_false h), ins_one]

lemma F_alive {x y : ℕ} (h : 4 * y ≤ 5 * x) (k : ℕ) :
    F (k + 1) x y = F k x (x + y) ++ (F k (x + y) y).tail := by
  unfold F
  rw [iterate_succ_apply, ins_cc, ite_eq_left_of_eq_true _ _ (eq_true h), ins_one]
  exact iter_split k [x] (x + y) [y]

/-- `w` is a prefix of `F k x y` for all large `k`. -/
def PF (x y : ℕ) (w : List ℕ) : Prop := ∃ K, ∀ k, K ≤ k → w <+: F k x y

lemma PF_nil (x y : ℕ) : PF x y [] := ⟨0, fun _ _ => List.nil_prefix⟩

lemma PF_step1 {x y : ℕ} {w : List ℕ} (h1 : 4 * y ≤ 5 * x) (h2 : x < 4 * y)
    (h : PF (x + y) y w) : PF x y (x :: w) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K + 1, fun k hk => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [F_alive h1, F_dead (by omega) k]
  obtain ⟨t, ht⟩ := iter_head k (x + y) [y]
  have ht' : F k (x + y) y = (x + y) :: t := ht
  have hw := hK k (by omega)
  rw [ht'] at hw ⊢
  show x :: w <+: x :: ((x + y) :: t)
  exact (List.prefix_cons_inj x).2 hw

lemma PF_step2 {x y : ℕ} {w : List ℕ} (h1 : 4 * y ≤ x) (h : PF x (x + y) w) : PF x y w := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K + 1, fun k hk => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [F_alive (by omega)]
  exact (hK k (by omega)).trans (List.prefix_append _ _)

/-- Blocks: from the pair `(A, d)` the outputs are `A, A+d, A+2d, A+3d`, then the
pair `(A+4d, A+5d)`. -/
def tv (A d : ℕ) : ℕ → ℕ
  | 0 => A
  | 1 => A + d
  | 2 => A + 2 * d
  | 3 => A + 3 * d
  | t + 4 => tv (A + 4 * d) (A + 5 * d) t

lemma tv_lt (A d i : ℕ) (hi : i ≤ 3) : tv A d i = A + i * d := by
  interval_cases i <;> simp [tv]

lemma PF_tv (m : ℕ) : ∀ A d i, 0 < d → A < d → i ≤ 3 → (1 ≤ i ∨ 4 * d ≤ 5 * A) →
    PF (A + i * d) d ((List.range m).map fun t => tv A d (i + t)) := by
  induction m with
  | zero =>
    intro A d i _ _ _ _
    simpa using PF_nil _ _
  | succ m ih =>
    intro A d i hd hA hi hc
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have e0 : tv A d (i + 0) = A + i * d := by rw [add_zero]; exact tv_lt A d i hi
    rw [e0]
    apply PF_step1
    · rcases hc with hc | hc
      · nlinarith
      · nlinarith
    · nlinarith
    · have hfun : ((fun t => tv A d (i + t)) ∘ Nat.succ) = fun t => tv A d ((i + 1) + t) := by
        funext t
        simp only [comp_apply, Nat.succ_eq_add_one]
        congr 1
        ring
      rw [hfun]
      rcases Nat.lt_or_ge i 3 with hi3 | hi3
      · have := ih A d (i + 1) hd hA (by omega) (Or.inl (by omega))
        rwa [show A + (i + 1) * d = A + i * d + d by ring] at this
      · have hi3' : i = 3 := by omega
        subst hi3'
        apply PF_step2 (by omega)
        have := ih (A + 4 * d) (A + 5 * d) 0 (by omega) (by omega) (by omega) (Or.inr (by omega))
        have hfun2 : (fun t => tv (A + 4 * d) (A + 5 * d) (0 + t)) =
            fun t => tv A d (3 + 1 + t) := by
          funext t
          rw [show 3 + 1 + t = t + 4 by ring, zero_add]
          simp [tv]
        rw [hfun2] at this
        rw [show A + 3 * d + d + d = A + 5 * d by ring,
          show A + 3 * d + d = A + 4 * d + 0 * (A + 5 * d) by ring]
        exact this

/-- The limit sequence: `a n` for `n ≥ 1` (and `a 0 = 0`). -/
def a (n : ℕ) : ℕ := tv 0 1 n

theorem limit_prefix (m : ℕ) :
    ∃ K, ∀ k, K ≤ k → ((List.range m).map fun t => a (t + 1)) <+: S k := by
  have h := PF_tv m 0 1 1 one_pos one_pos (by norm_num) (Or.inl le_rfl)
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun k hk => ?_⟩
  have e : (fun t => a (t + 1)) = fun t => tv 0 1 (1 + t) := by
    funext t
    simp [a, add_comm]
  rw [e]
  exact hK k hk

/-- **The limit exists**: position `n - 1` of `S k` is `a n` for all large `k`. -/
theorem A082981_limit (n : ℕ) (hn : 1 ≤ n) :
    ∃ K, ∀ k, K ≤ k → (S k)[n - 1]? = some (a n) := by
  obtain ⟨K, hK⟩ := limit_prefix n
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨u, hu⟩ := hK k hk
  rw [← hu, List.getElem?_append_left (by simp; omega)]
  simp only [List.getElem?_map, List.getElem?_range (by omega : n - 1 < n), Option.map_some]
  congr 2
  omega

/-! ### Block formula -/

def cd : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | j + 1 => ((cd j).1 + (cd j).2, 4 * (cd j).1 + 5 * (cd j).2)

def c (j : ℕ) : ℕ := (cd j).1
def d (j : ℕ) : ℕ := (cd j).2

lemma c_zero : c 0 = 0 := rfl
lemma d_zero : d 0 = 1 := rfl
lemma c_succ (j : ℕ) : c (j + 1) = c j + d j := rfl
lemma d_succ (j : ℕ) : d (j + 1) = 4 * c j + 5 * d j := rfl

lemma a_tv (j : ℕ) : ∀ t, a (4 * j + t) = tv (4 * c j) (d j) t := by
  induction j with
  | zero => intro t; simp [a, c_zero, d_zero]
  | succ j ih =>
    intro t
    rw [show 4 * (j + 1) + t = 4 * j + (t + 4) by ring, ih (t + 4)]
    simp only [tv, c_succ, d_succ]
    congr 1
    ring

/-- a(4j+t) = 4c(j) + t d(j) for t ≤ 3. -/
theorem a_block (j t : ℕ) (ht : t ≤ 3) : a (4 * j + t) = 4 * c j + t * d j := by
  rw [a_tv, tv_lt _ _ _ ht]

lemma cd_ge (j : ℕ) : 4 * c j ≤ d j ∧ 1 ≤ d j := by
  induction j with
  | zero => simp [c_zero, d_zero]
  | succ j ih => rw [c_succ, d_succ]; omega

lemma cd_inv (j : ℕ) : (d j : ℤ) ^ 2 - 4 * c j * d j - 4 * (c j : ℤ) ^ 2 = 1 := by
  induction j with
  | zero => simp [c_zero, d_zero]
  | succ j ih =>
    rw [c_succ, d_succ]
    push_cast
    linear_combination ih

lemma c_rec (n : ℕ) : (c (n + 2) : ℤ) = 6 * c (n + 1) - c n := by
  simp only [c_succ, d_succ]
  push_cast
  ring

lemma d_rec (n : ℕ) : (d (n + 2) : ℤ) = 6 * d (n + 1) - d n := by
  simp only [c_succ, d_succ]
  push_cast
  ring

/-- Two sequences with x(n+2) = 6x(n+1) - x(n) and equal first two terms agree. -/
lemma rec_eq (f g : ℕ → ℤ) (hf : ∀ n, f (n + 2) = 6 * f (n + 1) - f n)
    (hg : ∀ n, g (n + 2) = 6 * g (n + 1) - g n) (h0 : f 0 = g 0) (h1 : f 1 = g 1) :
    ∀ n, f n = g n := by
  have : ∀ n, f n = g n ∧ f (n + 1) = g (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ n ih => exact ⟨ih.2, by rw [hf, hg, ih.1, ih.2]⟩
  exact fun n => (this n).1

/-! ### The target sequences -/

/-- A038761: 1, 9, 53, ... -/
def A038761 : ℕ → ℤ
  | 0 => 1
  | 1 => 9
  | n + 2 => 6 * A038761 (n + 1) - A038761 n

/-- A002315: 1, 7, 41, ... -/
def A002315 : ℕ → ℤ
  | 0 => 1
  | 1 => 7
  | n + 2 => 6 * A002315 (n + 1) - A002315 n

/-- A005319: 0, 4, 24, ... -/
def A005319 : ℕ → ℤ
  | 0 => 0
  | 1 => 4
  | n + 2 => 6 * A005319 (n + 1) - A005319 n

/-- A001109: 0, 1, 6, ... -/
def A001109 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 6 * A001109 (n + 1) - A001109 n

/-- A077442 (offset 0): numbers x with 2x^2 + 7 a square, in increasing order. -/
noncomputable def A077442 (n : ℕ) : ℕ := Nat.nth (fun x => IsSquare (2 * x ^ 2 + 7)) n

/-- A077444 (offset 1): numbers k with (k^2 + 4)/2 a square, in increasing order. -/
noncomputable def A077444 (n : ℕ) : ℕ :=
  Nat.nth (fun k => 2 ∣ k ^ 2 + 4 ∧ IsSquare ((k ^ 2 + 4) / 2)) (n - 1)

/-- `Nat.nth p` is `f` when `f` is strictly increasing with range `{m | p m}`. -/
theorem nth_eq {p : ℕ → Prop} {f : ℕ → ℕ} (hf : StrictMono f)
    (hp : ∀ m, p m ↔ ∃ k, f k = m) (n : ℕ) : Nat.nth p n = f n := by
  have hinf : (Set.ofPred p).Infinite :=
    (Set.infinite_range_of_injective hf.injective).mono (by
      rintro _ ⟨k, rfl⟩
      exact (hp _).2 ⟨k, rfl⟩)
  have h := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := p) f ?_ ?_ (hf.strictMonoOn _)
  · exact (h (show n ∈ {n : ℕ | ∀ hf : (Set.ofPred p).Finite, n < hf.toFinset.card} from
      fun hfin => absurd hfin hinf)).symm
  · intro m hm
    obtain ⟨k, rfl⟩ := (hp m).1 hm
    exact ⟨k, fun hfin => absurd hfin hinf, rfl⟩
  · intro k _
    exact (hp _).2 ⟨k, rfl⟩

/-! ### Conjectures (2), (4), (5), (6): linear recurrences -/

/-- (2) a(4n+1) = A038761(n). -/
theorem conj2 (n : ℕ) : (a (4 * n + 1) : ℤ) = A038761 n := by
  rw [a_block n 1 (by norm_num)]
  push_cast
  refine rec_eq (fun n => 4 * (c n : ℤ) + 1 * d n) A038761 (fun n => ?_) (fun n => ?_) ?_ ?_ n
  · rw [c_rec, d_rec]
    ring
  · rfl
  · simp [c_zero, d_zero, A038761]
  · simp [c_succ, d_succ, c_zero, d_zero, A038761]

/-- (5) a(4n+4) = A005319(n+1). -/
theorem conj5 (n : ℕ) : (a (4 * n + 4) : ℤ) = A005319 (n + 1) := by
  rw [show 4 * n + 4 = 4 * (n + 1) + 0 by ring, a_block (n + 1) 0 (by norm_num)]
  push_cast
  refine rec_eq (fun n => 4 * (c n : ℤ) + 0 * d n) A005319 (fun n => ?_) (fun n => ?_) ?_ ?_ (n + 1)
  · rw [c_rec, d_rec]
    ring
  · rfl
  · simp [c_zero, d_zero, A005319]
  · simp [c_succ, d_succ, c_zero, d_zero, A005319]

/-- (6) a(4n+4)/4 = A001109(n+1), the division being exact. -/
theorem conj6 (n : ℕ) : 4 ∣ a (4 * n + 4) ∧ ((a (4 * n + 4) / 4 : ℕ) : ℤ) = A001109 (n + 1) := by
  rw [show 4 * n + 4 = 4 * (n + 1) + 0 by ring, a_block (n + 1) 0 (by norm_num)]
  simp only [zero_mul, add_zero]
  refine ⟨dvd_mul_right 4 _, ?_⟩
  rw [Nat.mul_div_cancel_left _ (by norm_num)]
  refine rec_eq (fun n => (c n : ℤ)) A001109 (fun n => ?_) (fun n => ?_) ?_ ?_ (n + 1)
  · exact c_rec n
  · rfl
  · simp [c_zero, A001109]
  · simp [c_succ, c_zero, d_zero, A001109]

/-- (4) a(4n+2)/2 = A002315(n), the division being exact. -/
theorem conj4 (n : ℕ) : 2 ∣ a (4 * n + 2) ∧ ((a (4 * n + 2) / 2 : ℕ) : ℤ) = A002315 n := by
  rw [a_block n 2 (by norm_num)]
  rw [show 4 * c n + 2 * d n = 2 * (2 * c n + d n) by ring]
  refine ⟨dvd_mul_right 2 _, ?_⟩
  rw [Nat.mul_div_cancel_left _ (by norm_num)]
  push_cast
  refine rec_eq (fun n => 2 * (c n : ℤ) + d n) A002315 (fun n => ?_) (fun n => ?_) ?_ ?_ n
  · rw [c_rec, d_rec]
    ring
  · rfl
  · simp [c_zero, d_zero, A002315]
  · simp [c_succ, d_succ, c_zero, d_zero, A002315]

/-! ### Conjecture (1): 2x^2 + 7 a square -/

/-- Every nonnegative solution of 2x^2 + 7 = y^2 is 4c(j) + d(j) or 4c(j) + 3d(j). -/
lemma sol1_complete : ∀ x : ℕ, ∀ y : ℤ, 0 ≤ y → 2 * (x : ℤ) ^ 2 + 7 = y ^ 2 →
    ∃ j, (x : ℤ) = 4 * c j + d j ∨ (x : ℤ) = 4 * c j + 3 * d j := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  intro y hy hxy
  by_cases hx : x ≤ 5
  · have hy9 : y < 9 := by
      have : (x : ℤ) ≤ 5 := by exact_mod_cast hx
      nlinarith
    interval_cases x <;> interval_cases y <;>
      first
      | (exfalso; norm_num at hxy; done)
      | (refine ⟨0, ?_⟩; norm_num [c_zero, d_zero])
  · rw [not_le] at hx
    have hx6 : (6 : ℤ) ≤ x := by exact_mod_cast hx
    have h1 : 2 * y < 3 * x := by nlinarith
    have h2 : (x : ℤ) < y := by nlinarith
    have h3 : 4 * (x : ℤ) ≤ 3 * y := by nlinarith
    have hpos : 0 ≤ 3 * (x : ℤ) - 2 * y := by linarith
    have hlt : (3 * (x : ℤ) - 2 * y).toNat < x := by omega
    have hsol : 2 * (((3 * (x : ℤ) - 2 * y).toNat : ℕ) : ℤ) ^ 2 + 7 = (3 * y - 4 * x) ^ 2 := by
      rw [Int.toNat_of_nonneg hpos]
      linear_combination hxy
    obtain ⟨j, hj⟩ := ih _ hlt (3 * y - 4 * x) (by linarith) hsol
    rw [Int.toNat_of_nonneg hpos] at hj
    have hge := cd_ge j
    have hinv := cd_inv j
    have hc0 : (0 : ℤ) ≤ c j := by positivity
    have hcd : 4 * (c j : ℤ) ≤ d j := by exact_mod_cast hge.1
    have e1 : (3 * y - 4 * x) ^ 2 = 2 * (3 * (x : ℤ) - 2 * y) ^ 2 + 7 := by
      linear_combination (-1 : ℤ) * hxy
    rcases hj with h | h
    · rw [h] at e1
      have e2 : (3 * (d j : ℤ) - 2 * c j) ^ 2 = 2 * (4 * (c j : ℤ) + d j) ^ 2 + 7 := by
        linear_combination 7 * hinv
      have hY : 3 * y - 4 * x = 3 * (d j : ℤ) - 2 * c j :=
        (pow_left_inj₀ (by linarith) (by linarith) two_ne_zero).1 (e1.trans e2.symm)
      refine ⟨j + 1, Or.inl ?_⟩
      rw [c_succ, d_succ]
      push_cast
      linear_combination 3 * h + 2 * hY
    · rw [h] at e1
      have e2 : (2 * (c j : ℤ) + 5 * d j) ^ 2 = 2 * (4 * (c j : ℤ) + 3 * d j) ^ 2 + 7 := by
        linear_combination 7 * hinv
      have hY : 3 * y - 4 * x = 2 * (c j : ℤ) + 5 * d j :=
        (pow_left_inj₀ (by linarith) (by positivity) two_ne_zero).1 (e1.trans e2.symm)
      refine ⟨j + 1, Or.inr ?_⟩
      rw [c_succ, d_succ]
      push_cast
      linear_combination 3 * h + 2 * hY

lemma a_odd_even (j : ℕ) : a (2 * (2 * j) + 1) = 4 * c j + d j := by
  rw [show 2 * (2 * j) + 1 = 4 * j + 1 by ring, a_block j 1 (by norm_num), one_mul]

lemma a_odd_odd (j : ℕ) : a (2 * (2 * j + 1) + 1) = 4 * c j + 3 * d j := by
  rw [show 2 * (2 * j + 1) + 1 = 4 * j + 3 by ring, a_block j 3 (by norm_num)]

/-- (1) a(2n+1) = A077442(n). -/
theorem conj1 (n : ℕ) : a (2 * n + 1) = A077442 n := by
  unfold A077442
  refine (nth_eq (f := fun n => a (2 * n + 1)) ?_ ?_ n).symm
  · apply strictMono_nat_of_lt_succ
    intro m
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
    · rw [a_odd_even, a_odd_odd]
      have := cd_ge j
      omega
    · rw [a_odd_odd, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, a_odd_even, c_succ, d_succ]
      have := cd_ge j
      omega
  · intro x
    constructor
    · rintro ⟨r, hr⟩
      obtain ⟨j, h | h⟩ := sol1_complete x r (by positivity) (by rw [sq (r : ℤ)]; exact_mod_cast hr)
      · exact ⟨2 * j, by rw [a_odd_even]; exact_mod_cast h.symm⟩
      · exact ⟨2 * j + 1, by rw [a_odd_odd]; exact_mod_cast h.symm⟩
    · rintro ⟨m, rfl⟩
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
      · rw [a_odd_even]
        have hge := cd_ge j
        refine ⟨3 * d j - 2 * c j, ?_⟩
        zify [show 2 * c j ≤ 3 * d j by omega]
        linear_combination (-7 : ℤ) * cd_inv j
      · rw [a_odd_odd]
        refine ⟨2 * c j + 5 * d j, ?_⟩
        zify
        linear_combination (-7 : ℤ) * cd_inv j

/-! ### Conjecture (3): (k^2 + 4)/2 a square -/

/-- Every nonnegative solution of k^2 + 4 = 2y^2 is 4c(j) + 2d(j). -/
lemma sol3_complete : ∀ k : ℕ, ∀ y : ℤ, 0 ≤ y → (k : ℤ) ^ 2 + 4 = 2 * y ^ 2 →
    ∃ j, (k : ℤ) = 4 * c j + 2 * d j := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro y hy hky
  by_cases hk : k ≤ 5
  · have hy9 : y < 9 := by
      have : (k : ℤ) ≤ 5 := by exact_mod_cast hk
      nlinarith
    interval_cases k <;> interval_cases y <;>
      first
      | (exfalso; norm_num at hky; done)
      | (refine ⟨0, ?_⟩; norm_num [c_zero, d_zero])
  · rw [not_le] at hk
    have hk6 : (6 : ℤ) ≤ k := by exact_mod_cast hk
    have h1 : 4 * y < 3 * k := by nlinarith
    have h2 : (k : ℤ) < 2 * y := by nlinarith
    have h3 : 2 * (k : ℤ) ≤ 3 * y := by nlinarith
    have hpos : 0 ≤ 3 * (k : ℤ) - 4 * y := by linarith
    have hlt : (3 * (k : ℤ) - 4 * y).toNat < k := by omega
    have hsol : (((3 * (k : ℤ) - 4 * y).toNat : ℕ) : ℤ) ^ 2 + 4 = 2 * (3 * y - 2 * k) ^ 2 := by
      rw [Int.toNat_of_nonneg hpos]
      linear_combination hky
    obtain ⟨j, hj⟩ := ih _ hlt (3 * y - 2 * k) (by linarith) hsol
    rw [Int.toNat_of_nonneg hpos] at hj
    have hinv := cd_inv j
    have hd0 : (0 : ℤ) ≤ d j := by positivity
    have e1 : 2 * (3 * y - 2 * k) ^ 2 = (3 * (k : ℤ) - 4 * y) ^ 2 + 4 := by
      linear_combination (-1 : ℤ) * hky
    rw [hj] at e1
    have e2 : 2 * (2 * (d j : ℤ)) ^ 2 = (4 * (c j : ℤ) + 2 * d j) ^ 2 + 4 := by
      linear_combination 4 * hinv
    have hY : 3 * y - 2 * k = 2 * (d j : ℤ) := by
      have : (3 * y - 2 * (k : ℤ)) ^ 2 = (2 * (d j : ℤ)) ^ 2 := by linarith
      exact (pow_left_inj₀ (by linarith) (by linarith) two_ne_zero).1 this
    refine ⟨j + 1, ?_⟩
    rw [c_succ, d_succ]
    push_cast
    linear_combination 3 * hj + 4 * hY

/-- (3) a(4n+2) = A077444(n+1). -/
theorem conj3 (n : ℕ) : a (4 * n + 2) = A077444 (n + 1) := by
  unfold A077444
  rw [Nat.add_sub_cancel]
  refine (nth_eq (f := fun n => a (4 * n + 2)) ?_ ?_ n).symm
  · apply strictMono_nat_of_lt_succ
    intro m
    rw [a_block m 2 (by norm_num), show 4 * (m + 1) + 2 = 4 * (m + 1) + 2 from rfl,
      a_block (m + 1) 2 (by norm_num), c_succ, d_succ]
    have := cd_ge m
    omega
  · intro k
    constructor
    · rintro ⟨h2, r, hr⟩
      have hk : (k : ℤ) ^ 2 + 4 = 2 * (r : ℤ) ^ 2 := by
        have : k ^ 2 + 4 = 2 * (r * r) := by rw [← hr]; exact (Nat.mul_div_cancel' h2).symm
        rw [sq (r : ℤ)]
        exact_mod_cast this
      obtain ⟨j, h⟩ := sol3_complete k r (by positivity) hk
      exact ⟨j, by rw [a_block j 2 (by norm_num)]; exact_mod_cast h.symm⟩
    · rintro ⟨m, rfl⟩
      rw [a_block m 2 (by norm_num)]
      have key : (4 * c m + 2 * d m) ^ 2 + 4 = 2 * ((2 * d m) * (2 * d m)) := by
        zify
        linear_combination (-4 : ℤ) * cd_inv m
      refine ⟨⟨_, key⟩, 2 * d m, ?_⟩
      rw [key, Nat.mul_div_cancel_left _ (by norm_num)]
