/-
NT-F31.2 (Guy, UPINT 3rd ed., F31): Coppersmith's claim that k = 247 is not
a quotient of two integers whose balanced-ternary digits are all +1 or -1.

Encoding: a nonempty list `es : List Bool` stands for the integer
`ev es = Σ dᵢ 3^i` with dᵢ = +1 (true) or -1 (false).  Because balanced
ternary representations are unique, "every balanced-ternary digit of m is
nonzero" is the same as "m = ev es for some nonempty es".

Checked here (core Lean, no Mathlib, `decide` on finite lists, `omega`):
* `no_multiplier`: for all nonempty es and all fs, 247 * ev es ≠ ev fs.
  That is, there is no m whose digits are all ±1 with 247 m also all ±1.
Method: read the product 247·m from the least significant digit with a
carry c, so that c + 247 e = f + 3 c'.  `T` is the set of carries reachable
after at least one digit (28 values, all with |c| ≤ 116); `D` ⊇ T is a set of
nonzero integers closed under stripping a ±1 digit, so no element of D is
the value of a ±1 digit string.
Not checked here: nothing beyond the encoding above.
-/

def dg (b : Bool) : Int := if b then 1 else -1

def ev : List Bool → Int
  | [] => 0
  | b :: bs => dg b + 3 * ev bs

def T : List Int :=
  [-116, -110, -104, -102, -98, -82, -68, -66, -62, -60, -50, -48, -46, -44,
   44, 46, 48, 50, 60, 62, 66, 68, 82, 98, 102, 104, 110, 116]

def D : List Int :=
  [-116, -110, -104, -102, -98, -82, -68, -66, -62, -60, -50, -48, -46, -44,
   -39, -37, -35, -33, -27, -23, -21, -17, -15, -12, -8, -6, -3, 3, 6, 8, 12,
   15, 17, 21, 23, 27, 33, 35, 37, 39, 44, 46, 48, 50, 60, 62, 66, 68, 82, 98,
   102, 104, 110, 116]

theorem T_closed : ∀ c ∈ T, ∀ e f : Bool,
    (c + 247 * dg e - dg f) % 3 = 0 → (c + 247 * dg e - dg f) / 3 ∈ T := by decide

theorem T_start : ∀ e f : Bool,
    (247 * dg e - dg f) % 3 = 0 → (247 * dg e - dg f) / 3 ∈ T := by decide

theorem T_bound : ∀ c ∈ T, -124 ≤ c ∧ c ≤ 124 := by decide

theorem T_sub_D : ∀ c ∈ T, c ∈ D := by decide

theorem D_closed : ∀ c ∈ D, c ≠ 0 ∧ ∀ f : Bool, (c - dg f) % 3 = 0 → (c - dg f) / 3 ∈ D := by
  decide

theorem dg_cases (b : Bool) : dg b = 1 ∨ dg b = -1 := by
  cases b <;> simp [dg]

theorem ev_cons (b : Bool) (bs : List Bool) : ev (b :: bs) = dg b + 3 * ev bs := rfl

theorem ev_ne_zero (b : Bool) (bs : List Bool) : ev (b :: bs) ≠ 0 := by
  rw [ev_cons]; have := dg_cases b; omega

/-- No element of `D` is the value of a ±1 digit string (empty string = 0). -/
theorem dead (fs : List Bool) : ∀ c ∈ D, ev fs ≠ c := by
  induction fs with
  | nil => intro c hc h; exact (D_closed c hc).1 (by simp [ev] at h; omega)
  | cons f fs ih =>
    intro c hc h
    rw [ev_cons] at h
    have h3 : (c - dg f) % 3 = 0 := by omega
    have hm := (D_closed c hc).2 f h3
    exact ih _ hm (by omega)

theorem carry (es : List Bool) : ∀ (fs : List Bool), ∀ c ∈ T, c + 247 * ev es ≠ ev fs := by
  induction es with
  | nil => intro fs c hc h; exact dead fs c (T_sub_D c hc) (by simp [ev] at h; omega)
  | cons e es ih =>
    intro fs c hc h
    have hb := T_bound c hc
    cases fs with
    | nil =>
      have h0 := ev_ne_zero e es
      simp only [ev] at h
      rw [ev_cons] at h0
      omega
    | cons f fs =>
      rw [ev_cons, ev_cons] at h
      have h3 : (c + 247 * dg e - dg f) % 3 = 0 := by omega
      have hm := T_closed c hc e f h3
      exact ih fs _ hm (by omega)

theorem no_multiplier (es fs : List Bool) (hne : es ≠ []) : 247 * ev es ≠ ev fs := by
  intro h
  cases es with
  | nil => exact hne rfl
  | cons e es =>
    cases fs with
    | nil =>
      have h0 := ev_ne_zero e es
      have h1 : ev ([] : List Bool) = 0 := rfl
      omega
    | cons f fs =>
      rw [ev_cons, ev_cons] at h
      have h3 : (247 * dg e - dg f) % 3 = 0 := by omega
      exact carry es fs _ (T_start e f h3) (by omega)
