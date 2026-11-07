/-
GEO-A4.4 (Croft–Falconer–Guy A4, Conway/Steinhaus): billiards in the regular tetrahedron.
Tetrahedron with vertices V_0..V_3 = (1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1); face f is the plane
n_f · x = 1 with n_f = -V_f.  The reflection in face f is x ↦ L_f x + t_f with
3 L_f = 3 I - 2 n_f n_fᵀ (an integer matrix `T3 f`).

Checked here (core Lean, no Mathlib):
* `trace_not_dvd`: for every cyclically reduced face word w = [f_1, …, f_k] (k ≥ 1, consecutive
  faces distinct, f_k ≠ f_1), the integer matrix P_w = (3L_{f_1})⋯(3L_{f_k}) = 3^k L_w has trace
  not divisible by 3.  Hence trace(L_w) ≠ 1 and L_w ≠ I (both would give trace(P_w) ∈ 3ℤ).
Not checked here (paper argument in README.md): that a periodic billiard trajectory with face
word w needs L_w u = u for its direction u, so for odd k L_w would be a reflection (trace 1) and a
continuous family would need L_w = I; hence every periodic orbit has an even number of bounces and
is isolated.  Also not checked: the computer search for orbits of length up to 20.
-/

abbrev Mat := Fin 3 → Fin 3 → Int

def nv : Fin 4 → Fin 3 → Int
  | 0 => fun i => [-1, -1, -1][i]!
  | 1 => fun i => [-1, 1, 1][i]!
  | 2 => fun i => [1, -1, 1][i]!
  | 3 => fun i => [1, 1, -1][i]!

def T3 (f : Fin 4) : Mat := fun i j => 3 * (if i = j then 1 else 0) - 2 * nv f i * nv f j

def mul (A B : Mat) : Mat := fun i j => A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j

def idm : Mat := fun i j => if i = j then 1 else 0

def tr (A : Mat) : Int := A 0 0 + A 1 1 + A 2 2

/-- P_w = (3 L_{f_1}) ⋯ (3 L_{f_k}). -/
def P : List (Fin 4) → Mat
  | [] => idm
  | f :: w => mul (T3 f) (P w)

def sg (b : Bool) : Int := if b then 1 else -1

/-- s · n_g n_hᵀ. -/
def outer (b : Bool) (g h : Fin 4) : Mat := fun i j => sg b * nv g i * nv h j

def cong3 (A B : Mat) : Prop := ∀ i j, A i j % 3 = B i j % 3

theorem mul_cong3 (M A B : Mat) (h : cong3 A B) : cong3 (mul M A) (mul M B) := by
  intro i j
  have e0 : (M i 0 * A 0 j) % 3 = (M i 0 * B 0 j) % 3 := by
    rw [Int.mul_emod, h 0 j, ← Int.mul_emod]
  have e1 : (M i 1 * A 1 j) % 3 = (M i 1 * B 1 j) % 3 := by
    rw [Int.mul_emod, h 1 j, ← Int.mul_emod]
  have e2 : (M i 2 * A 2 j) % 3 = (M i 2 * B 2 j) % 3 := by
    rw [Int.mul_emod, h 2 j, ← Int.mul_emod]
  simp only [mul]
  omega

/-- One reflection step mod 3: (3L_f) · (s n_g n_hᵀ) ≡ (-s) n_f n_hᵀ for f ≠ g. -/
theorem step_table : ∀ f g h : Fin 4, ∀ b : Bool, f ≠ g →
    ∀ i j : Fin 3, (mul (T3 f) (outer b g h)) i j % 3 = (outer (!b) f h) i j % 3 := by
  decide

theorem base_table : ∀ f : Fin 4, ∀ i j : Fin 3,
    (T3 f) i j % 3 = (outer true f f) i j % 3 := by
  decide

/-- Cyclically reduced words: consecutive letters distinct. -/
def chainNe : List (Fin 4) → Prop
  | [] => True
  | [_] => True
  | a :: b :: w => a ≠ b ∧ chainNe (b :: w)

def lastD : List (Fin 4) → Fin 4 → Fin 4
  | [], d => d
  | [a], _ => a
  | _ :: b :: w, d => lastD (b :: w) d

theorem lastD_default : ∀ (w : List (Fin 4)) (a d d' : Fin 4), lastD (a :: w) d = lastD (a :: w) d' := by
  intro w
  induction w with
  | nil => intro a d d'; rfl
  | cons b w ih => intro a d d'; exact ih b d d'

theorem mul_idm : ∀ f : Fin 4, ∀ i j : Fin 3, mul (T3 f) idm i j = T3 f i j := by
  decide

theorem len_flip (w : List (Fin 4)) (g : Fin 4) :
    ((g :: w).length % 2 == 0) = !(w.length % 2 == 0) := by
  simp only [List.length_cons]
  rcases Nat.mod_two_eq_zero_or_one w.length with h | h
  · have : (w.length + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (w.length + 1) % 2 = 0 := by omega
    simp [h, this]

theorem P_cong : ∀ (w : List (Fin 4)) (f : Fin 4), chainNe (f :: w) →
    cong3 (P (f :: w)) (outer (w.length % 2 == 0) f (lastD (f :: w) f)) := by
  intro w
  induction w with
  | nil =>
    intro f _ i j
    show mul (T3 f) idm i j % 3 = _
    rw [mul_idm]
    exact base_table f i j
  | cons g w ih =>
    intro f hc i j
    obtain ⟨hfg, hc'⟩ := hc
    have ih' := ih g hc'
    have h1 := mul_cong3 (T3 f) _ _ ih' i j
    have hlen := len_flip w g
    have hlast : lastD (f :: g :: w) f = lastD (g :: w) g := lastD_default w g f g
    show (mul (T3 f) (P (g :: w))) i j % 3 = _
    rw [h1, step_table f g _ _ hfg i j, hlen, hlast]

theorem dot_table : ∀ f h : Fin 4, ∀ b : Bool, f ≠ h →
    tr (outer b f h) % 3 ≠ 0 := by
  decide

/-- Main: for a cyclically reduced word (consecutive faces distinct, last ≠ first) the trace of
3^k L_w is not divisible by 3. -/
theorem trace_not_dvd (f : Fin 4) (w : List (Fin 4)) (hc : chainNe (f :: w))
    (hcyc : lastD (f :: w) f ≠ f) : tr (P (f :: w)) % 3 ≠ 0 := by
  have h := P_cong w f hc
  have e : tr (P (f :: w)) % 3 = tr (outer (w.length % 2 == 0) f (lastD (f :: w) f)) % 3 := by
    simp only [tr]
    have a := h 0 0; have b := h 1 1; have c := h 2 2
    omega
  rw [e]
  exact dot_table f _ _ (Ne.symm hcyc)

/-- Corollary: L_w is neither the identity nor of trace 1 (P_w = 3^k L_w). -/
theorem not_identity_not_reflection (f : Fin 4) (w : List (Fin 4)) (hc : chainNe (f :: w))
    (hcyc : lastD (f :: w) f ≠ f) :
    tr (P (f :: w)) ≠ 3 * 3 ^ (w.length + 1) ∧ tr (P (f :: w)) ≠ 3 ^ (w.length + 1) := by
  have h := trace_not_dvd f w hc hcyc
  constructor
  · intro e; rw [e] at h; apply h; simp [Int.mul_emod_right]
  · intro e; rw [e] at h; apply h
    rw [Int.pow_succ, Int.mul_emod_left]
