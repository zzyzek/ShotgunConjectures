/-
OEIS A086844 (Cloitre's conjecture, Aug 10 2003), checked with Mathlib.

For z ≥ 1 let r z = (z + √(z² + 4z)) / 2, and let b z m be the orbit
b 0 = m, b (k+1) = ⌊r z · b k⌋₊ (OEIS b(k+1) is our b k).  A086844 is the
set of odd m whose orbit is all odd, for z = 2, where r 2 = 1 + √3.
The conjecture says a(n) - 4n is ultimately periodic, with a = Nat.nth of
that set (a(n) = nth (n-1); the shift does not change periodicity).

Checked here:
* `floor_rec`   : ⌊r·⌊r x⌋₊⌋₊ = z⌊r x⌋₊ + z x - 1 for x ≥ 1, so the orbit
                  satisfies b(k+2) = z b(k+1) + z b(k) - 1.
* `inSeq_iff`   : m is a term iff m is odd and ⌊r m⌋₊ is odd.
* `not_eventually_periodic` : for every z ≥ 1 there are no P > 0 and N with
                  nth (n+P) = nth n + 4P for all n ≥ N, i.e. a(n) - 4n is
                  not ultimately periodic.
* `A086844_conjecture_false` : the case z = 2 with the literal 1 + √3.

Not checked in Lean: the listed data terms, and the finite witness
a(838) = 3363 (a(n) - 4n = 11 > 9) against the entry's remark
|a(n) - 4n| ≤ 9 (certificate/check_A086844.py).
-/
import Mathlib

open Real

namespace A086844

noncomputable def r (z : ℕ) : ℝ := ((z : ℝ) + √((z : ℝ) ^ 2 + 4 * z)) / 2

noncomputable def b (z m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => ⌊r z * (b z m k : ℝ)⌋₊

def InSeq (z m : ℕ) : Prop := Odd m ∧ ∀ k, Odd (b z m k)

lemma sq_bounds (z : ℕ) (hz : 1 ≤ z) :
    ((z : ℝ) + 1) ^ 2 < (z : ℝ) ^ 2 + 4 * z ∧ (z : ℝ) ^ 2 + 4 * z < ((z : ℝ) + 2) ^ 2 := by
  have : (1 : ℝ) ≤ z := by exact_mod_cast hz
  constructor <;> nlinarith

lemma not_square (z : ℕ) (hz : 1 ≤ z) : ¬ IsSquare (z ^ 2 + 4 * z) := by
  rintro ⟨k, hk⟩
  have h1 : (z + 1) ^ 2 < k * k := by rw [← hk]; nlinarith
  have h2 : k * k < (z + 2) ^ 2 := by rw [← hk]; nlinarith
  have a1 : z + 1 < k := by nlinarith
  have a2 : k < z + 2 := by nlinarith
  omega

lemma irr_sqrt (z : ℕ) (hz : 1 ≤ z) : Irrational √((z : ℝ) ^ 2 + 4 * z) := by
  have := irrational_sqrt_natCast_iff.mpr (not_square z hz)
  push_cast at this
  exact this

lemma irr_r (z : ℕ) (hz : 1 ≤ z) : Irrational (r z) := by
  unfold r
  have := ((irr_sqrt z hz).natCast_add z).div_natCast (m := 2) (by norm_num)
  simpa using this

lemma sqrt_bounds (z : ℕ) (hz : 1 ≤ z) :
    (z : ℝ) < √((z : ℝ) ^ 2 + 4 * z) ∧ √((z : ℝ) ^ 2 + 4 * z) < z + 2 := by
  obtain ⟨h1, h2⟩ := sq_bounds z hz
  have hz0 : (0 : ℝ) ≤ z := by positivity
  constructor
  · rw [Real.lt_sqrt hz0]; nlinarith
  · rw [Real.sqrt_lt' (by positivity)]; exact h2

lemma r_sq (z : ℕ) : r z ^ 2 = z * r z + z := by
  unfold r
  have h : √((z : ℝ) ^ 2 + 4 * z) ^ 2 = (z : ℝ) ^ 2 + 4 * z :=
    Real.sq_sqrt (by positivity)
  nlinarith [h]

lemma r_gap (z : ℕ) (hz : 1 ≤ z) : 0 < r z - z ∧ r z - z < 1 := by
  obtain ⟨h1, h2⟩ := sqrt_bounds z hz
  unfold r; constructor <;> linarith

lemma r_pos (z : ℕ) (hz : 1 ≤ z) : 0 < r z := by
  have := r_gap z hz; have : (0 : ℝ) ≤ z := by positivity
  linarith

/-- The fractional part of r·x is in (0,1) for x ≥ 1. -/
lemma frac_pos (z : ℕ) (hz : 1 ≤ z) (x : ℕ) (hx : 1 ≤ x) :
    (⌊r z * x⌋₊ : ℝ) < r z * x := by
  have hle : (⌊r z * x⌋₊ : ℝ) ≤ r z * x :=
    Nat.floor_le (by have := r_pos z hz; positivity)
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    have hirr : Irrational (r z * x) := (irr_r z hz).mul_natCast (by omega)
    exact hirr.ne_nat _ h.symm

theorem floor_rec (z : ℕ) (hz : 1 ≤ z) (x : ℕ) (hx : 1 ≤ x) :
    ⌊r z * (⌊r z * x⌋₊ : ℝ)⌋₊ = z * ⌊r z * x⌋₊ + z * x - 1 := by
  set c := ⌊r z * x⌋₊ with hc
  have hrp := r_pos z hz
  have hcle : (c : ℝ) < r z * x := frac_pos z hz x hx
  have hclt : r z * x < c + 1 := Nat.lt_floor_add_one _
  obtain ⟨g0, g1⟩ := r_gap z hz
  have hzx : 1 ≤ z * x := Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- r c = z c + z x - (r - z) f with f = r x - c in (0,1)
  have key : r z * c = z * c + z * x - (r z - z) * (r z * x - c) := by
    have := r_sq z; ring_nf; ring_nf at this; nlinarith [this]
  have lo : ((z * c + z * x - 1 : ℕ) : ℝ) < r z * c := by
    rw [Nat.cast_sub (by nlinarith)]; push_cast
    rw [key]; nlinarith [mul_lt_mul'' g1 (show r z * x - c < 1 by linarith)
      (le_of_lt g0) (by linarith)]
  have hi : r z * c < ((z * c + z * x - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub (by nlinarith)]; push_cast
    rw [key]; nlinarith [mul_pos g0 (show 0 < r z * x - c by linarith)]
  rw [Nat.floor_eq_iff (by positivity)]
  exact ⟨lo.le, hi⟩

lemma b_pos (z : ℕ) (hz : 1 ≤ z) (m : ℕ) (hm : 1 ≤ m) : ∀ k, 1 ≤ b z m k
  | 0 => hm
  | k + 1 => by
    have ih := b_pos z hz m hm k
    show 1 ≤ ⌊r z * (b z m k : ℝ)⌋₊
    apply Nat.le_floor
    have : (1 : ℝ) ≤ b z m k := by exact_mod_cast ih
    have := r_gap z hz; have : (1 : ℝ) ≤ z := by exact_mod_cast hz
    push_cast; nlinarith

lemma b_rec (z : ℕ) (hz : 1 ≤ z) (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    b z m (k + 2) = z * b z m (k + 1) + z * b z m k - 1 := by
  show ⌊r z * (⌊r z * (b z m k : ℝ)⌋₊ : ℝ)⌋₊ = _
  rw [floor_rec z hz _ (b_pos z hz m hm k)]; rfl

theorem inSeq_iff (z : ℕ) (hz : 1 ≤ z) (m : ℕ) :
    InSeq z m ↔ Odd m ∧ Odd ⌊r z * (m : ℝ)⌋₊ := by
  constructor
  · rintro ⟨hm, h⟩; exact ⟨hm, h 1⟩
  · rintro ⟨hm, h1⟩
    have hm1 : 1 ≤ m := by obtain ⟨j, rfl⟩ := hm; omega
    refine ⟨hm, ?_⟩
    have two : ∀ k, Odd (b z m k) ∧ Odd (b z m (k + 1)) := by
      intro k
      induction k with
      | zero => exact ⟨hm, h1⟩
      | succ k ih =>
        refine ⟨ih.2, ?_⟩
        rw [b_rec z hz m hm1 k]
        have hp := b_pos z hz m hm1 k
        obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := ih
        rw [hu, hv]
        refine ⟨z * (u + v + 1) - 1, ?_⟩
        have : 1 ≤ z * (u + v + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
        have e : z * (2 * v + 1) + z * (2 * u + 1) = 2 * (z * (u + v + 1)) := by ring
        omega
    exact fun k => (two k).1

/-- Parity of the floor difference forces r·Q rational. -/
lemma no_even_shift (z : ℕ) (hz : 1 ≤ z) (Q M : ℕ) (hQ : 0 < Q) (hQe : Even Q)
    (h : ∀ m, M ≤ m → Odd m →
      (Odd ⌊r z * (m : ℝ)⌋₊ ↔ Odd ⌊r z * ((m + Q : ℕ) : ℝ)⌋₊)) : False := by
  set F : ℕ → ℤ := fun m => (⌊r z * (m : ℝ)⌋₊ : ℤ) with hF
  have hrp := r_pos z hz
  have Fle : ∀ m : ℕ, (F m : ℝ) ≤ r z * m ∧ r z * m < F m + 1 := by
    intro m; simp only [hF, Int.cast_natCast]
    exact ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩
  -- the difference at odd m ≥ M is even and lies in (rQ - 1, rQ + 1)
  have dEven : ∀ m, M ≤ m → Odd m → Even (F (m + Q) - F m) := by
    intro m hm ho
    have := h m hm ho
    simp only [hF]
    rcases Nat.even_or_odd ⌊r z * (m : ℝ)⌋₊ with he | he
    · have h2 : ¬ Odd ⌊r z * ((m + Q : ℕ) : ℝ)⌋₊ := fun hh =>
        (Nat.not_odd_iff_even.mpr he) (this.mpr hh)
      rw [Nat.not_odd_iff_even] at h2
      obtain ⟨a, ha⟩ := he; obtain ⟨c, hc⟩ := h2
      exact ⟨(c : ℤ) - a, by rw [ha, hc]; push_cast; ring⟩
    · obtain ⟨a, ha⟩ := he; obtain ⟨c, hc⟩ := this.mp ⟨a, ha⟩
      exact ⟨(c : ℤ) - a, by rw [ha, hc]; push_cast; ring⟩
  have dBnd : ∀ m : ℕ, |((F (m + Q) - F m : ℤ) : ℝ) - r z * Q| < 1 := by
    intro m
    obtain ⟨a1, a2⟩ := Fle m; obtain ⟨b1, b2⟩ := Fle (m + Q)
    push_cast at b1 b2 ⊢
    rw [abs_lt]; constructor <;> nlinarith
  -- base point
  set m0 := 2 * M + 1
  have hm0o : ∀ t : ℕ, Odd (m0 + t * Q) := by
    intro t; obtain ⟨q, hq⟩ := hQe
    exact ⟨M + t * q, by rw [hq]; ring⟩
  set E := F (m0 + Q) - F m0
  have dConst : ∀ t : ℕ, F (m0 + t * Q + Q) - F (m0 + t * Q) = E := by
    intro t
    have e1 := dEven (m0 + t * Q) (by omega) (hm0o t)
    have e2 := dEven m0 (by omega) (by simpa using hm0o 0)
    have b1 := dBnd (m0 + t * Q); have b2 := dBnd m0
    have hE : (E : ℝ) = ((F (m0 + Q) - F m0 : ℤ) : ℝ) := by simp only [E]
    rw [abs_lt] at b1 b2
    have hlt : |((F (m0 + t * Q + Q) - F (m0 + t * Q) - E : ℤ) : ℝ)| < 2 := by
      rw [abs_lt]; push_cast at b1 b2 hE ⊢; constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]
    have hlt' : |F (m0 + t * Q + Q) - F (m0 + t * Q) - E| < 2 := by exact_mod_cast hlt
    obtain ⟨u, hu⟩ := e1; obtain ⟨v, hv⟩ := e2
    rw [abs_lt] at hlt'
    simp only [E] at hlt' ⊢
    omega
  have lin : ∀ t : ℕ, F (m0 + t * Q) = F m0 + t * E := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have := dConst t
      rw [show m0 + (t + 1) * Q = m0 + t * Q + Q by ring]
      push_cast; linarith
  -- so t (rQ - E) stays in (-1, 1) for every t
  have small : ∀ t : ℕ, |(t : ℝ) * (r z * Q - E)| < 1 := by
    intro t
    obtain ⟨a1, a2⟩ := Fle m0; obtain ⟨b1, b2⟩ := Fle (m0 + t * Q)
    have := lin t
    have hc : (F (m0 + t * Q) : ℝ) = F m0 + t * E := by exact_mod_cast this
    push_cast at b1 b2
    rw [hc] at b1 b2
    rw [abs_lt]; constructor <;> nlinarith
  have hzero : r z * Q - E = 0 := by
    by_contra hne
    have hpos : 0 < |r z * Q - E| := abs_pos.mpr hne
    obtain ⟨t, ht⟩ := exists_nat_gt (1 / |r z * Q - E|)
    have := small t
    rw [abs_mul, Nat.abs_cast] at this
    have : (1 / |r z * Q - E|) * |r z * Q - E| < t * |r z * Q - E| :=
      mul_lt_mul_of_pos_right ht hpos
    rw [one_div_mul_cancel hpos.ne'] at this
    linarith
  have hirr := (irr_r z hz).mul_natCast (m := Q) (by omega)
  exact hirr.ne_int E (by linarith)

theorem not_eventually_periodic (z : ℕ) (hz : 1 ≤ z) :
    ¬ ∃ P N : ℕ, 0 < P ∧ ∀ n, N ≤ n → Nat.nth (InSeq z) (n + P) = Nat.nth (InSeq z) n + 4 * P := by
  rintro ⟨P, N, hP, hper⟩
  have hinf : (Set.ofPred (InSeq z)).Infinite := by
    intro hf
    set c := hf.toFinset.card
    have := hper (N + c) (by omega)
    rw [Nat.nth_of_card_le hf (show c ≤ N + c + P by omega),
      Nat.nth_of_card_le hf (show c ≤ N + c by omega)] at this
    omega
  have mono := Nat.nth_strictMono hinf
  have rng := Nat.range_nth_of_infinite hinf
  have memOf : ∀ x, InSeq z x → ∃ n, Nat.nth (InSeq z) n = x := by
    intro x hx
    have : x ∈ Set.range (Nat.nth (InSeq z)) := by rw [rng]; exact hx
    exact this
  set M := Nat.nth (InSeq z) N
  have shift : ∀ m, M ≤ m → (InSeq z m ↔ InSeq z (m + 4 * P)) := by
    intro m hm
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := memOf m hx
      have hNn : N ≤ n := by
        by_contra hlt; rw [not_le] at hlt
        have := mono hlt; omega
      rw [← hn, ← hper n hNn]
      exact Nat.nth_mem_of_infinite hinf _
    · intro hx
      obtain ⟨n, hn⟩ := memOf _ hx
      have hNn : N + P ≤ n := by
        by_contra hlt; rw [not_le] at hlt
        have := mono hlt
        rw [hper N le_rfl] at this; omega
      have := hper (n - P) (by omega)
      rw [show n - P + P = n by omega, hn] at this
      have e : m = Nat.nth (InSeq z) (n - P) := by omega
      rw [e]; exact Nat.nth_mem_of_infinite hinf _
  apply no_even_shift z hz (4 * P) M (by omega) ⟨2 * P, by ring⟩
  intro m hm ho
  have := shift m hm
  rw [inSeq_iff z hz, inSeq_iff z hz] at this
  have ho' : Odd (m + 4 * P) := by
    obtain ⟨j, hj⟩ := ho; exact ⟨j + 2 * P, by omega⟩
  constructor
  · intro h1; exact (this.mp ⟨ho, h1⟩).2
  · intro h1; exact (this.mpr ⟨ho', h1⟩).2

lemma r_two : r 2 = 1 + √3 := by
  unfold r
  have : √((2 : ℕ) ^ 2 + 4 * (2 : ℕ) : ℝ) = 2 * √3 := by
    rw [show ((2 : ℕ) ^ 2 + 4 * (2 : ℕ) : ℝ) = 2 ^ 2 * 3 by norm_num,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  push_cast at this ⊢
  rw [this]; ring

/-- A086844 with its own definition: b(1) = m, b(k) = ⌊(1+√3) b(k-1)⌋. -/
noncomputable def orbit (m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => ⌊(1 + √3) * (orbit m k : ℝ)⌋₊

def A086844Pred (m : ℕ) : Prop := Odd m ∧ ∀ k, Odd (orbit m k)

lemma orbit_eq (m : ℕ) : ∀ k, orbit m k = b 2 m k
  | 0 => rfl
  | k + 1 => by
    show ⌊(1 + √3) * (orbit m k : ℝ)⌋₊ = ⌊r 2 * (b 2 m k : ℝ)⌋₊
    rw [orbit_eq m k, r_two]

theorem A086844_conjecture_false :
    ¬ ∃ P N : ℕ, 0 < P ∧ ∀ n, N ≤ n →
      Nat.nth A086844Pred (n + P) = Nat.nth A086844Pred n + 4 * P := by
  have : A086844Pred = InSeq 2 := by
    funext m; simp only [A086844Pred, InSeq, orbit_eq]
  rw [this]; exact not_eventually_periodic 2 (by norm_num)

end A086844

open A086844
