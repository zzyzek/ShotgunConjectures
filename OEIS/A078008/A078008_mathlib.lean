import Mathlib

/-!
# OEIS A078008: even denominators in the rows of the Farey (Stern-Brocot) tree on (0,1)

Reading. The "infinite Farey row of 2^n terms" is row n of the Stern-Brocot (Farey) tree of (0,1): row 0 is
1/2, and each fraction (a+c)/(b+d), the mediant of its Farey neighbours a/b < c/d, has the two children
(2a+c)/(2b+d) (mediant of a/b and itself) and (a+2c)/(b+2d). A node is stored as (a, b, c, d).

Definitions.
* `A078008` : a(0) = 1, a(1) = 0, a(n+2) = a(n+1) + 2 a(n) (the recurrence of the g.f. (1-x)/((1+x)(1-2x))).
* `row n` : the 2^n nodes of row n; the fraction of (a,b,c,d) is (a+c)/(b+d).
* `evenDen n` : the number of fractions in row n with even denominator.

Main result.
* `A078008_farey : evenDen n = A078008 n` for all n.

Checked: everything above. Not checked: that the recurrence equals the g.f. definition (coefficient
comparison), and that `row n` is the Stern-Brocot row (this is its definition by mediants).
-/

def A078008 : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => A078008 (n + 1) + 2 * A078008 n

def children (x : ℕ × ℕ × ℕ × ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  [(x.1, x.2.1, x.1 + x.2.2.1, x.2.1 + x.2.2.2), (x.1 + x.2.2.1, x.2.1 + x.2.2.2, x.2.2.1, x.2.2.2)]

def row : ℕ → List (ℕ × ℕ × ℕ × ℕ)
  | 0 => [(0, 1, 1, 1)]
  | n + 1 => (row n).flatMap children

def isEven (x : ℕ × ℕ × ℕ × ℕ) : Bool := (x.2.1 + x.2.2.2) % 2 == 0

def evenDen (n : ℕ) : ℕ := (row n).countP isEven

/-- Farey neighbours: b c = a d + 1. -/
def FareyInv (x : ℕ × ℕ × ℕ × ℕ) : Prop := x.2.1 * x.2.2.1 = x.1 * x.2.2.2 + 1

lemma inv_children (x : ℕ × ℕ × ℕ × ℕ) (hx : FareyInv x) : ∀ y ∈ children x, FareyInv y := by
  obtain ⟨a, b, c, d⟩ := x
  simp only [FareyInv] at hx
  simp only [children, List.mem_cons, List.mem_nil_iff, or_false]
  rintro y (rfl | rfl) <;> simp only [FareyInv] <;> nlinarith

lemma inv_row (n : ℕ) : ∀ y ∈ row n, FareyInv y := by
  induction n with
  | zero => simp [row, FareyInv]
  | succ n ih =>
    intro y hy
    simp only [row, List.mem_flatMap] at hy
    obtain ⟨x, hx, hy⟩ := hy
    exact inv_children x (ih x hx) y hy

lemma node_count (a b c d : ℕ) (h : FareyInv (a, b, c, d)) :
    (children (a, b, c, d)).countP isEven + (if isEven (a, b, c, d) then 1 else 0) = 1 := by
  simp only [FareyInv] at h
  have hbd : ¬ (b % 2 = 0 ∧ d % 2 = 0) := by
    rintro ⟨hb, hd⟩
    have h1 : (b * c) % 2 = 0 := by rw [Nat.mul_mod, hb]; simp
    have h2 : (a * d) % 2 = 0 := by rw [Nat.mul_mod, hd]; simp
    omega
  simp only [children, isEven, List.countP_cons, List.countP_nil, beq_iff_eq]
  split_ifs <;> simp_all <;> omega

lemma step (L : List (ℕ × ℕ × ℕ × ℕ)) (hL : ∀ y ∈ L, FareyInv y) :
    (L.flatMap children).length = 2 * L.length ∧
    (L.flatMap children).countP isEven + L.countP isEven = L.length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have ih' := ih (fun y hy => hL y (List.mem_cons_of_mem x hy))
    obtain ⟨a, b, c, d⟩ := x
    have hn := node_count a b c d (hL _ List.mem_cons_self)
    simp only [List.flatMap_cons, List.length_append, List.countP_append, List.countP_cons,
      List.length_cons]
    have hlen : (children (a, b, c, d)).length = 2 := rfl
    rw [hlen]
    constructor
    · omega
    · have := ih'.2
      split_ifs at hn ⊢ <;> omega

lemma row_facts (n : ℕ) : (row n).length = 2 ^ n ∧ evenDen (n + 1) + evenDen n = 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h1 := step (row n) (inv_row n)
    have h2 := step (row (n + 1)) (inv_row (n + 1))
    simp only [row] at h1 h2 ⊢
    unfold evenDen; simp only [row]
    rw [pow_succ]
    constructor
    · rw [h1.1, ih.1]; ring
    · rw [h2.2, h1.1, ih.1]; ring

lemma A078008_add (n : ℕ) : A078008 (n + 1) + A078008 n = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [A078008]; rw [pow_succ]; omega

theorem A078008_farey (n : ℕ) : evenDen n = A078008 n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := (row_facts n).2
    have h' := A078008_add n
    omega
