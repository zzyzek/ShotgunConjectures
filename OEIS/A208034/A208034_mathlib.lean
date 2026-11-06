import Mathlib

/-
OEIS A208034 (P. D. Hanna, 2012): g.f. exp(Σ_{n≥1} 2 Pell(n)^2 x^n/n), Pell = A000129.
Conjectures in the entry, for all positive integers k:
(1) exp(Σ 2 Pell(n)^(2k) x^n/n) is an integer series;
(2) exp(Σ 2 Pell(n)^(2k-1) x^n/n) is NOT an integer series;
(3) exp(Σ Pell(n)^(2k) x^n/n) is NOT an integer series.

Definitions.
* `pell`: Pell(0) = 0, Pell(1) = 1, Pell(n+2) = 2 Pell(n+1) + Pell(n) (A000129).
* `expCoeff b n`: coefficients of exp(Σ b(n) x^n/n), given by A(0) = 1 and
  (n+1) A(n+1) = Σ_{j=0..n} b(j+1) A(n-j) (equivalently x A' = (Σ b(n) x^n) A), over ℚ.

Main theorems.
* `A208034_conj1 k n : ∃ z : ℤ, expCoeff (bseq k) n = z`, bseq k n = 2 Pell(n)^(2k) (all k ≥ 0;
  `A208034_int` is the entry itself, k = 1).
* `A208034_conj2 k (hk : 1 ≤ k) : ¬ ∃ z : ℤ, expCoeff (fun n => 2 * pell n ^ (2k-1)) 3 = z`.
* `A208034_conj3 k (hk : 1 ≤ k) : ¬ ∃ z : ℤ, expCoeff (fun n => pell n ^ (2k)) 2 = z`.

Route for (1) (adapted from OEIS/A207969, the Fibonacci analogue; the power-series part
and the Dwork lemma are copied unchanged).
* `Zs`: the ring ℤ[√2]; α = 1 + √2, α^n = H(n) + Pell(n) √2, trace `tr` = 2a, norm a² - 2b².
  `frob`: for p odd prime, z^p ≡ τ z (mod p) with τ = id or conjugation (2^((p-1)/2) ≡ ±1).
  `lucas_gauss`: Q(m p^a) ≡ Q(m p^(a-1)) (mod p^a) for Q(n) = tr(α^n).
* `eight_pell_sq`: 8 Pell(n)^2 = Q(2n) - 2(-1)^n satisfies the congruences at odd p, hence so
  does 2 (8 Pell(n)^2)^k = 8^k b(n); divide by the unit 8^k mod p. For p = 2: 2^j | n ⇒ 2^j | Pell(n) (Pell(2m) = 2 Pell(m) H(m)),
  so 2^a divides b(m 2^a) and b(m 2^(a-1)).
* `dwork` + `expCoeff_int_of_euler`: Gauss congruences ⇒ Euler product ⇒ integer coefficients.
(2), (3): the coefficient of x^3 is (4 + 6·2^m + 2·5^m)/3 with m = 2k-1 odd (≡ 2 mod 3), and the
coefficient of x^2 is (1 + 4^k)/2.
Checked: all of the above, for all k and n. Not checked: that `expCoeff` is the OEIS
"exp(...)" (standard characterisation, stated above). Axioms: propext, Classical.choice, Quot.sound.
-/

namespace OEIS_A208034

/-- Pell numbers A000129 -/
def pell : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * pell (n + 1) + pell n

/-- `ℤ[√2]`: the pair `⟨a, b⟩` is `a + b √2`. -/
@[ext] structure Zs where
  a : ℤ
  b : ℤ

namespace Zs

instance : Add Zs := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Mul Zs := ⟨fun x y => ⟨x.a * y.a + 2 * (x.b * y.b), x.a * y.b + x.b * y.a⟩⟩
instance : Neg Zs := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub Zs := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
instance : Zero Zs := ⟨⟨0, 0⟩⟩
instance : One Zs := ⟨⟨1, 0⟩⟩

@[simp] theorem add_a (x y : Zs) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : Zs) : (x + y).b = x.b + y.b := rfl
@[simp] theorem mul_a (x y : Zs) : (x * y).a = x.a * y.a + 2 * (x.b * y.b) := rfl
@[simp] theorem mul_b (x y : Zs) : (x * y).b = x.a * y.b + x.b * y.a := rfl
@[simp] theorem neg_a (x : Zs) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : Zs) : (-x).b = -x.b := rfl
@[simp] theorem sub_a (x y : Zs) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : Zs) : (x - y).b = x.b - y.b := rfl
@[simp] theorem zero_a : (0 : Zs).a = 0 := rfl
@[simp] theorem zero_b : (0 : Zs).b = 0 := rfl
@[simp] theorem one_a : (1 : Zs).a = 1 := rfl
@[simp] theorem one_b : (1 : Zs).b = 0 := rfl

instance : CommRing Zs where
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp <;> ring
  mul_assoc := by intros; ext <;> simp <;> ring
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp
  zero_mul := by intros; ext <;> simp
  mul_zero := by intros; ext <;> simp
  left_distrib := by intros; ext <;> simp <;> ring
  right_distrib := by intros; ext <;> simp <;> ring
  mul_comm := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp
  sub_eq_add_neg := by intros; ext <;> simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem natCast_eq (n : ℕ) : (n : Zs) = ⟨n, 0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.cast_succ, ih]; ext <;> simp

theorem intCast_eq (n : ℤ) : (n : Zs) = ⟨n, 0⟩ := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simp [natCast_eq]
  · rw [Int.cast_neg, Int.cast_natCast, natCast_eq]; ext <;> simp

theorem dvd_iff (q : ℤ) (z : Zs) : (q : Zs) ∣ z ↔ q ∣ z.a ∧ q ∣ z.b := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [intCast_eq]
    exact ⟨⟨w.a, by simp⟩, ⟨w.b, by simp⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    refine ⟨⟨u, v⟩, ?_⟩
    rw [intCast_eq]; ext <;> simp [hu, hv]

/-- √2 -/
def s : Zs := ⟨0, 1⟩

/-- α = 1 + √2 -/
def alpha : Zs := ⟨1, 1⟩

/-- conjugation √2 ↦ -√2 -/
def sig : Zs →+* Zs where
  toFun x := ⟨x.a, -x.b⟩
  map_one' := by ext <;> simp
  map_mul' := by intros; ext <;> simp; ring
  map_zero' := by ext <;> simp
  map_add' := by intros; ext <;> simp; ring

def tr (x : Zs) : ℤ := 2 * x.a

theorem tr_sig (x : Zs) : tr (sig x) = tr x := by simp [tr, sig]

theorem tr_sub (x y : Zs) : tr (x - y) = tr x - tr y := by simp [tr]; ring

theorem dvd_tr (q : ℤ) (z : Zs) (h : (q : Zs) ∣ z) : q ∣ tr z := by
  rw [dvd_iff] at h
  exact dvd_mul_of_dvd_right h.1 _

/-- companion Pell numbers as traces -/
def Q (n : ℕ) : ℤ := tr (alpha ^ n)

theorem fermat_int (p : ℕ) (hp : p.Prime) (x : ℤ) : (p : ℤ) ∣ x ^ p - x := by
  have := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.pow_card, sub_self]

theorem decomp (z : Zs) : z = (z.a : Zs) + (z.b : Zs) * s := by
  ext <;> simp [intCast_eq, s]

theorem int_dvd_cast (q x : ℤ) (h : q ∣ x) : (q : Zs) ∣ (x : Zs) := by
  obtain ⟨w, rfl⟩ := h; exact ⟨w, by push_cast; ring⟩

/-- Frobenius: for p an odd prime there is τ ∈ {id, σ} with z^p ≡ τ z (mod p). -/
theorem frob (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    ∃ τ : Zs →+* Zs, (∀ x, tr (τ x) = tr x) ∧ ∀ z : Zs, (p : Zs) ∣ z ^ p - τ z := by
  have hs : ∃ τ : Zs →+* Zs, (∀ x, tr (τ x) = tr x) ∧ (p : Zs) ∣ s ^ p - τ s := by
    obtain ⟨j, hj⟩ := hp.eq_two_or_odd'.resolve_left h2
    have hs2 : s ^ 2 = ((2 : ℤ) : Zs) := by rw [intCast_eq]; ext <;> simp [s, pow_two]
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have h2p : (p : ℤ) ∣ 2 ^ (2 * j) - 1 := by
      have h := fermat_int p hp 2
      have e2 : (2 : ℤ) ^ p - 2 = 2 * (2 ^ (2 * j) - 1) := by rw [hj]; ring
      rw [e2] at h
      rcases hpz.dvd_or_dvd h with h' | h'
      · exfalso
        have h22 : p ∣ 2 := by exact_mod_cast h'
        rcases (Nat.prime_two.eq_one_or_self_of_dvd p h22) with h1 | h1
        · exact hp.one_lt.ne' h1
        · exact h2 h1
      · exact h'
    have hfac : (2 : ℤ) ^ (2 * j) - 1 = (2 ^ j - 1) * (2 ^ j + 1) := by ring
    rw [hfac] at h2p
    have hsp : s ^ p = s * ((2 ^ j : ℤ) : Zs) := by
      rw [hj, pow_succ, pow_mul, hs2]; push_cast; ring
    rcases hpz.dvd_or_dvd h2p with ⟨t, ht⟩ | ⟨t, ht⟩
    · refine ⟨RingHom.id _, fun _ => rfl, ⟨s * (t : Zs), ?_⟩⟩
      have he : ((2 ^ j : ℤ) : Zs) = 1 + (p : Zs) * (t : Zs) := by
        rw [show (2 : ℤ) ^ j = 1 + p * t by linarith]; push_cast; ring
      rw [hsp, he]; simp; ring
    · refine ⟨sig, tr_sig, ⟨s * (t : Zs), ?_⟩⟩
      have he : ((2 ^ j : ℤ) : Zs) = -1 + (p : Zs) * (t : Zs) := by
        rw [show (2 : ℤ) ^ j = -1 + p * t by linarith]; push_cast; ring
      have hsig : sig s = -s := by ext <;> simp [sig, s]
      rw [hsp, he, hsig]; ring
  obtain ⟨τ, htr, hτ⟩ := hs
  refine ⟨τ, htr, fun z => ?_⟩
  obtain ⟨A, B⟩ := z
  have hz : (⟨A, B⟩ : Zs) = (A : Zs) + (B : Zs) * s := decomp _
  rw [hz]
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (A : Zs) ((B : Zs) * s)
  have eq : ((A : Zs) + (B : Zs) * s) ^ p - τ ((A : Zs) + (B : Zs) * s) =
      ((A ^ p - A : ℤ) : Zs) + ((B ^ p - B : ℤ) : Zs) * s ^ p +
      (B : Zs) * (s ^ p - τ s) + (p : Zs) * ((A : Zs) * ((B : Zs) * s) * r) := by
    rw [hr]; simp only [map_add, map_mul, map_intCast]; push_cast; ring
  rw [eq]
  refine dvd_add (dvd_add (dvd_add ?_ ?_) ?_) (dvd_mul_right _ _)
  · exact int_dvd_cast _ _ (fermat_int p hp _)
  · exact dvd_mul_of_dvd_left (int_dvd_cast _ _ (fermat_int p hp _)) _
  · exact dvd_mul_of_dvd_right hτ _

theorem lucas_gauss (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (a m : ℕ) (ha : 1 ≤ a) :
    ((p : ℤ) ^ a) ∣ Q (m * p ^ a) - Q (m * p ^ (a - 1)) := by
  obtain ⟨τ, htr, hτ⟩ := frob p hp h2
  have h := dvd_sub_pow_of_dvd_sub (hτ (alpha ^ m)) (a - 1)
  rw [show a - 1 + 1 = a by omega] at h
  have e1 : ((alpha ^ m) ^ p) ^ p ^ (a - 1) = alpha ^ (m * p ^ a) := by
    rw [← pow_mul, ← pow_mul, show p * p ^ (a - 1) = p ^ a by
      rw [← pow_succ']; congr 1; omega]
  have e2 : (τ (alpha ^ m)) ^ p ^ (a - 1) = τ (alpha ^ (m * p ^ (a - 1))) := by
    rw [← map_pow, ← pow_mul]
  rw [e1, e2] at h
  have := dvd_tr ((p : ℤ) ^ a) _ (by push_cast; exact h)
  rw [tr_sub, htr] at this
  exact this

theorem alpha_sq : alpha ^ 2 = alpha + alpha + 1 := by
  ext <;> simp [alpha, pow_two]

/-- α^n = H(n) + Pell(n) √2 -/
theorem alpha_pow_b (n : ℕ) : (alpha ^ n).b = pell n ∧ (alpha ^ (n + 1)).b = pell (n + 1) := by
  induction n with
  | zero => simp [pell, alpha]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have e : alpha ^ (n + 1 + 1) = alpha ^ (n + 1) + alpha ^ (n + 1) + alpha ^ n := by
      rw [show n + 1 + 1 = n + 2 by ring, pow_add, alpha_sq, pow_succ]; ring
    rw [e, show pell (n + 1 + 1) = 2 * pell (n + 1) + pell n from rfl]
    simp only [add_b]
    rw [ih.1, ih.2]; ring

theorem alpha_pow_b' (n : ℕ) : (alpha ^ n).b = pell n := (alpha_pow_b n).1

/-- norm -/
def N (x : Zs) : ℤ := x.a ^ 2 - 2 * x.b ^ 2

theorem N_mul (x y : Zs) : N (x * y) = N x * N y := by simp [N]; ring

theorem N_alpha_pow (n : ℕ) : N (alpha ^ n) = (-1) ^ n := by
  induction n with
  | zero => simp [N]
  | succ n ih => rw [pow_succ, N_mul, ih, pow_succ]; simp [N, alpha]

theorem eight_pell_sq (n : ℕ) : 8 * pell n ^ 2 = Q (2 * n) - 2 * (-1) ^ n := by
  rw [← N_alpha_pow, Q, pow_mul', ← alpha_pow_b' n]
  simp [N, tr, pow_two]; ring

theorem pell_two_mul (m : ℕ) : pell (2 * m) = 2 * pell m * (alpha ^ m).a := by
  rw [← alpha_pow_b', ← alpha_pow_b', pow_mul', pow_two]; simp; ring

theorem two_pow_dvd_pell (j m : ℕ) : (2 : ℤ) ^ j ∣ pell (2 ^ j * m) := by
  induction j generalizing m with
  | zero => simp
  | succ j ih =>
    rw [show 2 ^ (j + 1) * m = 2 * (2 ^ j * m) by ring, pell_two_mul, pow_succ']
    obtain ⟨w, hw⟩ := ih m
    rw [hw]; exact ⟨w * (alpha ^ (2 ^ j * m)).a, by ring⟩

end Zs

open PowerSeries

/-- θ = x d/dx -/
noncomputable def theta (f : ℤ⟦X⟧) : ℤ⟦X⟧ := PowerSeries.mk fun n => (n : ℤ) * coeff n f

theorem coeff_theta (f : ℤ⟦X⟧) (n : ℕ) : coeff n (theta f) = n * coeff n f := by
  simp [theta]

theorem theta_mul (f g : ℤ⟦X⟧) : theta (f * g) = theta f * g + f * theta g := by
  ext n
  rw [coeff_theta, map_add, coeff_mul, coeff_mul, coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [coeff_theta, coeff_theta, ← hx']
  push_cast; ring

/-- log-derivative relation θ f = B f -/
def LD (f B : ℤ⟦X⟧) : Prop := theta f = B * f

theorem LD_mul {f g B C : ℤ⟦X⟧} (h1 : LD f B) (h2 : LD g C) : LD (f * g) (B + C) := by
  unfold LD at *; rw [theta_mul, h1, h2]; ring

theorem theta_one : theta 1 = 0 := by
  ext n; rw [coeff_theta, coeff_one]; split_ifs with h <;> simp [h]

theorem LD_one : LD 1 0 := by unfold LD; rw [theta_one]; ring

theorem LD_pow {f B : ℤ⟦X⟧} (h : LD f B) (n : ℕ) : LD (f ^ n) ((n : ℤ⟦X⟧) * B) := by
  induction n with
  | zero => simpa using LD_one
  | succ n ih =>
    rw [pow_succ]
    have := LD_mul ih h
    convert this using 1; push_cast; ring

theorem LD_inv {f g B : ℤ⟦X⟧} (h : LD f B) (hfg : f * g = 1) : LD g (-B) := by
  unfold LD at *
  have h0 := congrArg theta hfg
  rw [theta_mul, theta_one, h] at h0
  calc theta g = (f * g) * theta g := by rw [hfg, one_mul]
    _ = g * (B * f * g + f * theta g) - g * B * (f * g) := by ring
    _ = -B * g := by rw [h0, hfg]; ring

/-- W d = Σ_j X^(d j) -/
noncomputable def Wd (d : ℕ) : ℤ⟦X⟧ := PowerSeries.mk fun n => if d ∣ n then 1 else 0

theorem Wd_mul (d : ℕ) (hd : 1 ≤ d) : (1 - X ^ d) * Wd d = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_one]
  simp only [Wd, coeff_mk]
  have hiff : d ∣ n ↔ (d ≤ n ∧ d ∣ n - d) ∨ n = 0 := by
    constructor
    · intro h
      by_cases hn : n = 0
      · exact Or.inr hn
      · exact Or.inl ⟨Nat.le_of_dvd (by omega) h, Nat.dvd_sub h (dvd_refl d)⟩
    · rintro (⟨h1, h2⟩ | h)
      · have := Nat.dvd_add h2 (dvd_refl d); rwa [Nat.sub_add_cancel h1] at this
      · rw [h]; exact dvd_zero d
  by_cases hn : n = 0
  · subst hn; simp; omega
  · by_cases h : d ∣ n
    · have h' := (hiff.mp h).resolve_right hn
      simp [h, h'.1, h'.2, hn]
    · have h' : ¬ (d ≤ n ∧ d ∣ n - d) := fun h' => h (hiff.mpr (Or.inl h'))
      by_cases h1 : d ≤ n
      · have h2 : ¬ d ∣ n - d := fun h2 => h' ⟨h1, h2⟩
        simp [h, h1, h2, hn]
      · simp [h, h1, hn]

noncomputable def Gd (d : ℕ) : ℤ⟦X⟧ := (d : ℤ⟦X⟧) * X ^ d * Wd d

theorem theta_one_sub (d : ℕ) (hd1 : 1 ≤ d) : theta (1 - X ^ d) = -((d : ℤ⟦X⟧) * X ^ d) := by
  ext n
  rw [coeff_theta, map_sub, coeff_one, coeff_X_pow, map_neg, ← map_natCast (C (R := ℤ)) d,
    coeff_C_mul, coeff_X_pow]
  by_cases h0 : n = 0
  · subst h0; simp; omega
  · by_cases hd : n = d
    · subst hd; simp [h0]
    · simp [h0, hd]

theorem LD_one_sub (d : ℕ) (hd : 1 ≤ d) : LD (1 - X ^ d) (-Gd d) := by
  unfold LD Gd
  rw [theta_one_sub d hd]
  have := Wd_mul d hd
  calc -((d : ℤ⟦X⟧) * X ^ d) = -((d : ℤ⟦X⟧) * X ^ d) * ((1 - X ^ d) * Wd d) := by rw [this, mul_one]
    _ = _ := by ring

theorem LD_Wd (d : ℕ) (hd : 1 ≤ d) : LD (Wd d) (Gd d) := by
  have := LD_inv (LD_one_sub d hd) (Wd_mul d hd)
  rwa [neg_neg] at this

noncomputable def Fdc (d : ℕ) (c : ℤ) : ℤ⟦X⟧ :=
  if 0 ≤ c then Wd d ^ c.toNat else (1 - X ^ d) ^ (-c).toNat

theorem LD_Fdc (d : ℕ) (hd : 1 ≤ d) (c : ℤ) : LD (Fdc d c) ((c : ℤ⟦X⟧) * Gd d) := by
  unfold Fdc
  split_ifs with hc
  · have := LD_pow (LD_Wd d hd) c.toNat
    convert this using 2
    rw [show (c.toNat : ℤ⟦X⟧) = ((c.toNat : ℤ) : ℤ⟦X⟧) by push_cast; rfl, Int.toNat_of_nonneg hc]
  · have := LD_pow (LD_one_sub d hd) (-c).toNat
    convert this using 1
    rw [show ((-c).toNat : ℤ⟦X⟧) = (((-c).toNat : ℤ) : ℤ⟦X⟧) by push_cast; rfl,
      Int.toNat_of_nonneg (by omega)]
    push_cast; ring

theorem const_Wd (d : ℕ) : constantCoeff (Wd d) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp [Wd]

theorem const_Fdc (d : ℕ) (hd : 1 ≤ d) (c : ℤ) : constantCoeff (Fdc d c) = 1 := by
  unfold Fdc
  split_ifs
  · rw [map_pow, const_Wd, one_pow]
  · rw [map_pow, map_sub, map_one, map_pow, constantCoeff_X, zero_pow (by omega), sub_zero,
      one_pow]

/-- truncated Euler product ∏_{d ≤ D} (1 - x^d)^(-c d) -/
noncomputable def EP (c : ℕ → ℤ) (D : ℕ) : ℤ⟦X⟧ := ∏ i ∈ Finset.range D, Fdc (i + 1) (c (i + 1))

noncomputable def EB (c : ℕ → ℤ) (D : ℕ) : ℤ⟦X⟧ :=
  ∑ i ∈ Finset.range D, (c (i + 1) : ℤ⟦X⟧) * Gd (i + 1)

theorem LD_EP (c : ℕ → ℤ) (D : ℕ) : LD (EP c D) (EB c D) := by
  induction D with
  | zero => simpa [EP, EB] using LD_one
  | succ D ih =>
    unfold EP EB
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    exact LD_mul ih (LD_Fdc (D + 1) (by omega) _)

theorem const_EP (c : ℕ → ℤ) (D : ℕ) : constantCoeff (EP c D) = 1 := by
  unfold EP
  rw [map_prod]
  exact Finset.prod_eq_one (fun i _ => const_Fdc (i + 1) (by omega) _)

theorem coeff_Gd (d n : ℕ) (hd : 1 ≤ d) :
    coeff n (Gd d) = if 0 < n ∧ d ∣ n then (d : ℤ) else 0 := by
  unfold Gd
  rw [← map_natCast (C (R := ℤ)) d, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  simp only [Wd, coeff_mk]
  by_cases h1 : d ≤ n
  · simp only [h1, ↓reduceIte]
    have hiff : d ∣ n - d ↔ (0 < n ∧ d ∣ n) := by
      constructor
      · intro h; refine ⟨by omega, ?_⟩
        have := Nat.dvd_add h (dvd_refl d); rwa [Nat.sub_add_cancel h1] at this
      · rintro ⟨_, h⟩; exact Nat.dvd_sub h (dvd_refl d)
    by_cases h2 : 0 < n ∧ d ∣ n
    · simp [h2, hiff.mpr h2]
    · have h3 : ¬ d ∣ n - d := fun h => h2 (hiff.mp h)
      simp only [h2, h3, ↓reduceIte, mul_zero]
  · have h2 : ¬ (0 < n ∧ d ∣ n) := fun ⟨h0, h⟩ => h1 (Nat.le_of_dvd h0 h)
    simp only [h1, h2, ↓reduceIte, mul_zero]

theorem coeff_EB (c : ℕ → ℤ) (D n : ℕ) (hn : 1 ≤ n) (hD : n ≤ D) :
    coeff n (EB c D) = ∑ d ∈ n.divisors, (d : ℤ) * c d := by
  unfold EB
  rw [map_sum]
  simp_rw [← map_intCast (C (R := ℤ)), coeff_C_mul]
  rw [Finset.sum_congr rfl (fun x _ => by rw [coeff_Gd (x + 1) n (by omega)])]
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun x _ => x + 1) (fun d _ => d - 1) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    simp only [Nat.mem_divisors]
    exact ⟨hx.2.2, by omega⟩
  · intro d hd
    simp only [Nat.mem_divisors] at hd
    have := Nat.le_of_dvd (by omega) hd.1
    have h1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.sub_add_cancel h1]; exact hd.1
  · intro x _; simp
  · intro d hd
    simp only [Nat.mem_divisors] at hd
    have h1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
    omega
  · intro x _; push_cast; ring


/-! ## exp(Σ b_n x^n / n) and its coefficients -/

/-- Coefficients of `exp (∑_{n ≥ 1} b n * x^n / n)`: the unique series `A` with `A 0 = 1` and
`x A' = (∑ b n x^n) A`, i.e. `(n+1) A_{n+1} = ∑_{j=0}^{n} b (j+1) A_{n-j}`. -/
def expCoeff (b : ℕ → ℤ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => (∑ j : Fin (n + 1), (b (j + 1) : ℚ) * expCoeff b (n - j)) / (n + 1)
decreasing_by omega

theorem LD_rec (f B : ℤ⟦X⟧) (h : LD f B) (hf : constantCoeff f = 1) (n : ℕ) :
    ((n + 1 : ℕ) : ℤ) * coeff (n + 1) f =
      ∑ j ∈ Finset.range (n + 1), coeff (j + 1) B * coeff (n - j) f := by
  have h0 : coeff 0 B = 0 := by
    have := congrArg (coeff 0) h
    rw [coeff_theta, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      map_mul, hf, ← coeff_zero_eq_constantCoeff_apply] at this
    simpa using this.symm
  have := congrArg (coeff (n + 1)) h
  rw [coeff_theta, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ'] at this
  simp only [h0, zero_mul, add_zero] at this
  rw [this]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [show n + 1 - (j + 1) = n - j by omega]

theorem expCoeff_eq (b : ℕ → ℤ) (f B : ℤ⟦X⟧) (h : LD f B) (hf : constantCoeff f = 1) (D : ℕ)
    (hB : ∀ j, 1 ≤ j → j ≤ D → coeff j B = b j) : ∀ n, n ≤ D → expCoeff b n = coeff n f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | n
    · simp [expCoeff, coeff_zero_eq_constantCoeff_apply, hf]
    · rw [expCoeff]
      have hr := LD_rec f B h hf n
      have hq : ((n + 1 : ℕ) : ℚ) * ((coeff (n + 1) f : ℤ) : ℚ) =
          ∑ j ∈ Finset.range (n + 1), ((coeff (j + 1) B : ℤ) : ℚ) * ((coeff (n - j) f : ℤ) : ℚ) := by
        exact_mod_cast hr
      rw [Fin.sum_univ_eq_sum_range (fun j => (b (j + 1) : ℚ) * expCoeff b (n - j)) (n + 1)]
      have hsum : ∑ j ∈ Finset.range (n + 1), (b (j + 1) : ℚ) * expCoeff b (n - j) =
          ∑ j ∈ Finset.range (n + 1), ((coeff (j + 1) B : ℤ) : ℚ) * ((coeff (n - j) f : ℤ) : ℚ) :=
        Finset.sum_congr rfl (fun j hj => by
          rw [Finset.mem_range] at hj
          rw [ih (n - j) (by omega) (by omega), hB (j + 1) (by omega) (by omega)])
      rw [hsum, ← hq]
      push_cast
      field_simp

theorem expCoeff_int_of_euler (b c : ℕ → ℤ)
    (h : ∀ n, 1 ≤ n → b n = ∑ d ∈ n.divisors, (d : ℤ) * c d) (n : ℕ) :
    ∃ z : ℤ, expCoeff b n = z :=
  ⟨coeff n (EP c n), expCoeff_eq b _ _ (LD_EP c n) (const_EP c n) n
    (fun j h1 h2 => by rw [coeff_EB c n j h1 h2, h j h1]) n le_rfl⟩

/-! ## Gauss congruences give an Euler product (Dwork) -/

/-- local Gauss congruence at `p` -/
def LGp (p : ℕ) (b : ℕ → ℤ) : Prop :=
  ∀ a m, 1 ≤ a → ((p : ℤ) ^ a) ∣ b (m * p ^ a) - b (m * p ^ (a - 1))

def cOf (b : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 0 else (b n - ∑ d ∈ n.properDivisors.attach, (d.1 : ℤ) * cOf b d.1) / n
termination_by n
decreasing_by exact (Nat.mem_properDivisors.mp d.2).2

theorem cOf_eq (b : ℕ → ℤ) (n : ℕ) (hn : n ≠ 0) :
    cOf b n = (b n - ∑ d ∈ n.properDivisors, (d : ℤ) * cOf b d) / n := by
  rw [cOf]
  simp only [hn, ↓reduceIte]
  congr 2
  exact Finset.sum_attach n.properDivisors (fun d => (d : ℤ) * cOf b d)

theorem dvd_of_prime_pows (n : ℕ) (hn : n ≠ 0) (X : ℤ)
    (h : ∀ p : ℕ, p.Prime → ((p : ℤ) ^ n.factorization p) ∣ X) : (n : ℤ) ∣ X := by
  by_cases hX : X = 0
  · rw [hX]; exact dvd_zero _
  have hX' : X.natAbs ≠ 0 := by simpa using hX
  rw [Int.ofNat_dvd_left]
  apply (Nat.factorization_prime_le_iff_dvd hn hX').mp
  intro p hp
  have := h p hp
  rw [← Int.natCast_pow, Int.ofNat_dvd_left] at this
  exact (hp.pow_dvd_iff_le_factorization hX').mp this

theorem pow_dvd_of_not_dvd (p v m d : ℕ) (hp : p.Prime) (hv : 1 ≤ v) (hm : ¬ p ∣ m)
    (hd : d ∣ m * p ^ v) (hnd : ¬ d ∣ m * p ^ (v - 1)) : p ^ v ∣ d := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h1 := Nat.eq_zero_of_zero_dvd hd
    have hpv : p ^ v ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hm0 : m = 0 := by
      rcases Nat.mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hpv
    exact hnd (by rw [hm0, zero_mul])
  obtain ⟨e, d', hpd', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 p hp.one_lt.ne'
  have hcop : Nat.Coprime (p ^ v) d' := (Nat.Coprime.pow_left v ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd'))
  have hd'm : d' ∣ m := by
    have : d' ∣ m * p ^ v := Dvd.dvd.trans (Dvd.intro_left _ rfl) hd
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop.symm this)
  have hem : p ^ e ∣ p ^ v := by
    have : p ^ e ∣ m * p ^ v := Dvd.dvd.trans (Dvd.intro _ rfl) hd
    have hc2 : Nat.Coprime (p ^ e) m := Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
    exact hc2.dvd_of_dvd_mul_left this
  have hle : e ≤ v := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hem
  by_cases hev : e = v
  · subst hev; exact Dvd.intro _ rfl
  · exfalso; apply hnd
    have : p ^ e ∣ p ^ (v - 1) := Nat.pow_dvd_pow p (by omega)
    rw [mul_comm m]
    exact mul_dvd_mul this hd'm

theorem dwork (b : ℕ → ℤ) (hLG : ∀ p : ℕ, p.Prime → LGp p b) :
    ∀ n, 1 ≤ n → b n = ∑ d ∈ n.divisors, (d : ℤ) * cOf b d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    set S := ∑ d ∈ n.properDivisors, (d : ℤ) * cOf b d with hS
    have hdvd : (n : ℤ) ∣ b n - S := by
      apply dvd_of_prime_pows n (by omega)
      intro p hp
      set v := n.factorization p with hv
      by_cases hv0 : v = 0
      · rw [hv0, pow_zero]; exact one_dvd _
      set m := n / p ^ v with hm
      have hnm : n = m * p ^ v := by
        rw [hm, hv, mul_comm]; exact (Nat.ordProj_mul_ordCompl_eq_self n p).symm
      have hpm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp (by omega)
      set n' := m * p ^ (v - 1) with hn'
      have hn'n : n' ∣ n := by
        rw [hnm]; exact mul_dvd_mul_left m (Nat.pow_dvd_pow p (by omega))
      have hm0 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h] at hnm; omega
        · exact h
      have hn'lt : n' < n := by
        rw [hnm, hn']
        have : p ^ (v - 1) < p ^ v := Nat.pow_lt_pow_right hp.one_lt (by omega)
        exact Nat.mul_lt_mul_of_pos_left this (by omega)
      have hIH := ih n' hn'lt (by
        have : 1 ≤ p ^ (v - 1) := Nat.one_le_pow _ _ hp.pos
        rw [hn']; nlinarith)
      have hsub : n'.divisors ⊆ n.properDivisors := by
        intro d hd
        rw [Nat.mem_divisors] at hd
        rw [Nat.mem_properDivisors]
        exact ⟨hd.1.trans hn'n, lt_of_le_of_lt (Nat.le_of_dvd (by omega) hd.1) hn'lt⟩
      have hsplit := Finset.sum_sdiff hsub (f := fun d : ℕ => (d : ℤ) * cOf b d)
      have hX : b n - S = (b (m * p ^ v) - b (m * p ^ (v - 1))) -
          ∑ d ∈ (n.properDivisors \ n'.divisors : Finset ℕ), (d : ℤ) * cOf b d := by
        rw [hS, ← hsplit, ← hIH, ← hnm, hn']; ring
      rw [hX]
      apply dvd_sub (hLG p hp v m (by omega))
      apply Finset.dvd_sum
      intro d hd
      rw [Finset.mem_sdiff, Nat.mem_properDivisors, Nat.mem_divisors] at hd
      apply dvd_mul_of_dvd_left
      have := pow_dvd_of_not_dvd p v m d hp (by omega) hpm (by rw [← hnm]; exact hd.1.1)
        (fun h => hd.2 ⟨h, by rw [hn']; exact Nat.ne_of_gt (Nat.mul_pos hm0 (pow_pos hp.pos _))⟩)
      exact_mod_cast this
    rw [← Nat.insert_self_properDivisors (by omega : n ≠ 0),
      Finset.sum_insert Nat.self_notMem_properDivisors, ← hS, cOf_eq b n (by omega)]
    rw [Int.mul_ediv_cancel' hdvd]; ring

/-! ## closure of the local Gauss congruence -/

theorem LGp_mul {p : ℕ} {f g : ℕ → ℤ} (hf : LGp p f) (hg : LGp p g) : LGp p (fun n => f n * g n) := by
  intro a m ha
  have e : f (m * p ^ a) * g (m * p ^ a) - f (m * p ^ (a - 1)) * g (m * p ^ (a - 1)) =
      f (m * p ^ a) * (g (m * p ^ a) - g (m * p ^ (a - 1))) +
      (f (m * p ^ a) - f (m * p ^ (a - 1))) * g (m * p ^ (a - 1)) := by ring
  simp only; rw [e]
  exact dvd_add (dvd_mul_of_dvd_right (hg a m ha) _) (dvd_mul_of_dvd_left (hf a m ha) _)

theorem LGp_pow {p : ℕ} {f : ℕ → ℤ} (hf : LGp p f) (k : ℕ) : LGp p (fun n => f n ^ k) := by
  induction k with
  | zero => intro a m _; simp
  | succ k ih =>
    have := LGp_mul ih hf
    simpa [pow_succ] using this

theorem LGp_sub {p : ℕ} {f g : ℕ → ℤ} (hf : LGp p f) (hg : LGp p g) : LGp p (fun n => f n - g n) := by
  intro a m ha
  have e : f (m * p ^ a) - g (m * p ^ a) - (f (m * p ^ (a - 1)) - g (m * p ^ (a - 1))) =
      (f (m * p ^ a) - f (m * p ^ (a - 1))) - (g (m * p ^ a) - g (m * p ^ (a - 1))) := by ring
  simp only; rw [e]
  exact dvd_sub (hf a m ha) (hg a m ha)

theorem LGp_const_mul {p : ℕ} {f : ℕ → ℤ} (hf : LGp p f) (c : ℤ) : LGp p (fun n => c * f n) := by
  intro a m ha
  simp only; rw [← mul_sub]
  exact dvd_mul_of_dvd_right (hf a m ha) _

theorem LGp_neg_one (p : ℕ) (hp : p.Prime) : LGp p (fun n => (-1 : ℤ) ^ n) := by
  intro a m ha
  simp only
  rcases hp.eq_two_or_odd' with rfl | hodd
  · by_cases ha1 : a = 1
    · subst ha1
      rw [show m * 2 ^ 1 = m * 2 by ring, show m * 2 ^ (1 - 1) = m by simp, pow_mul]
      rcases neg_one_pow_eq_or ℤ m with h | h <;> rw [h] <;> norm_num
    · have e1 : Even (m * 2 ^ a) := by
        rw [show a = (a - 1) + 1 by omega, pow_succ]; exact ⟨m * 2 ^ (a - 1), by ring⟩
      have e2 : Even (m * 2 ^ (a - 1)) := by
        rw [show a - 1 = (a - 2) + 1 by omega, pow_succ]; exact ⟨m * 2 ^ (a - 2), by ring⟩
      rw [e1.neg_one_pow, e2.neg_one_pow, sub_self]; exact dvd_zero _
  · have hpa : Odd (p ^ a) := hodd.pow
    have hpa1 : Odd (p ^ (a - 1)) := hodd.pow
    have : (-1 : ℤ) ^ (m * p ^ a) = (-1) ^ (m * p ^ (a - 1)) := by
      rw [pow_mul, pow_mul]
      rcases neg_one_pow_eq_or ℤ m with h | h <;> rw [h] <;> simp [hpa.neg_one_pow, hpa1.neg_one_pow]
    rw [this, sub_self]; exact dvd_zero _

/-! ## the sequence 2 Pell(n)^(2k) -/

open Zs

/-- `b n = 2 * Pell(n)^(2k)` -/
def bseq (k n : ℕ) : ℤ := 2 * pell n ^ (2 * k)

theorem two_pow_dvd_bseq (k a N : ℕ) (hk : 1 ≤ k) (h : (2 : ℤ) ^ (a - 1) ∣ pell N) :
    (2 : ℤ) ^ a ∣ bseq k N := by
  obtain ⟨t, ht⟩ := h
  unfold bseq
  rw [ht, mul_pow, ← pow_mul, ← mul_assoc, ← pow_succ']
  apply dvd_mul_of_dvd_left
  apply pow_dvd_pow
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · omega
  · have : a - 1 ≤ (a - 1) * (2 * k) := Nat.le_mul_of_pos_right _ (by omega)
    omega

theorem LG_bseq (k : ℕ) : ∀ p : ℕ, p.Prime → LGp p (bseq k) := by
  intro p hp
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · intro a m _; simp [bseq, hk0]
  by_cases h2 : p = 2
  · subst h2
    intro a m ha
    apply dvd_sub
    · apply two_pow_dvd_bseq k a _ hk
      have := two_pow_dvd_pell a m
      rw [mul_comm m]
      exact (pow_dvd_pow 2 (by omega)).trans this
    · apply two_pow_dvd_bseq k a _ hk
      rw [mul_comm m]
      exact two_pow_dvd_pell (a - 1) m
  · have hL : LGp p (fun n => Q (2 * n)) := by
      intro a m ha
      have := lucas_gauss p hp h2 a (2 * m) ha
      simp only; rw [← mul_assoc, ← mul_assoc]; exact this
    have hs : LGp p (fun n => 8 * pell n ^ 2) := by
      have := LGp_sub hL (LGp_const_mul (LGp_neg_one p hp) 2)
      have e : (fun n => 8 * pell n ^ 2) = (fun n => Q (2 * n) - 2 * (-1) ^ n) := by
        funext n; exact eight_pell_sq n
      rw [e]; exact this
    have hsk := LGp_const_mul (LGp_pow hs k) 2
    intro a m ha
    have h1 := hsk a m ha
    have e : ∀ N, 2 * (8 * pell N ^ 2) ^ k = 8 ^ k * bseq k N := by
      intro N; unfold bseq
      rw [mul_pow, ← pow_mul]; ring
    simp only [e] at h1
    rw [← mul_sub] at h1
    have hcop : IsCoprime ((p : ℤ) ^ a) ((8 : ℤ) ^ k) := by
      rw [show (8 : ℤ) ^ k = 2 ^ (3 * k) by rw [pow_mul]; norm_num]
      apply IsCoprime.pow
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr h2
      show Int.gcd (p : ℤ) ((2 : ℕ) : ℤ) = 1
      rw [Int.gcd_natCast_natCast]; exact this
    exact hcop.dvd_of_dvd_mul_left h1

/-- Conjecture (1) of A208034: `exp (∑_{n ≥ 1} 2 Pell(n)^(2k) x^n / n)` has integer
coefficients for every `k` (stated for k ≥ 1 in the entry; also true for k = 0). -/
theorem A208034_conj1 (k n : ℕ) : ∃ z : ℤ, expCoeff (bseq k) n = z :=
  expCoeff_int_of_euler (bseq k) (cOf (bseq k)) (dwork _ (LG_bseq k)) n

/-- The entry itself (k = 1): A208034 is an integer sequence. -/
theorem A208034_int (n : ℕ) : ∃ z : ℤ, expCoeff (bseq 1) n = z := A208034_conj1 1 n

theorem expCoeff_one (b : ℕ → ℤ) : expCoeff b 1 = b 1 := by
  rw [expCoeff]; simp [expCoeff]

theorem expCoeff_zero (b : ℕ → ℤ) : expCoeff b 0 = 1 := by rw [expCoeff]

theorem expCoeff_two (b : ℕ → ℤ) : expCoeff b 2 = ((b 1 : ℚ) ^ 2 + b 2) / 2 := by
  rw [expCoeff, Fin.sum_univ_two]
  simp [expCoeff_zero, expCoeff_one]
  ring

theorem expCoeff_three (b : ℕ → ℤ) :
    expCoeff b 3 = ((b 1 : ℚ) * (((b 1 : ℚ) ^ 2 + b 2) / 2) + (b 2 : ℚ) * b 1 + b 3) / 3 := by
  rw [expCoeff, Fin.sum_univ_three]
  simp [expCoeff_zero, expCoeff_one, expCoeff_two]
  ring

theorem pell_one : pell 1 = 1 := rfl
theorem pell_two : pell 2 = 2 := rfl
theorem pell_three : pell 3 = 5 := rfl

/-- Conjecture (3) of A208034: `exp (∑ Pell(n)^(2k) x^n / n)` is not an integer series (k ≥ 1):
its coefficient of x^2 is (1 + 4^k)/2. -/
theorem A208034_conj3 (k : ℕ) (hk : 1 ≤ k) :
    ¬ ∃ z : ℤ, expCoeff (fun n => pell n ^ (2 * k)) 2 = z := by
  rintro ⟨z, hz⟩
  rw [expCoeff_two, pell_one, pell_two] at hz
  have h : (1 : ℤ) + 2 ^ (2 * k) = 2 * z := by
    have : ((1 : ℤ) : ℚ) + ((2 : ℤ) ^ (2 * k) : ℤ) = ((2 * z : ℤ) : ℚ) := by
      push_cast; rw [← hz]; push_cast; ring
    exact_mod_cast this
  have h4 : (2 : ℤ) ^ (2 * k) = 2 * 2 ^ (2 * k - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

/-- Conjecture (2) of A208034: `exp (∑ 2 Pell(n)^(2k-1) x^n / n)` is not an integer series
(k ≥ 1): its coefficient of x^3 is (4 + 6·2^m + 2·5^m)/3 with m = 2k - 1 odd. -/
theorem A208034_conj2 (k : ℕ) (hk : 1 ≤ k) :
    ¬ ∃ z : ℤ, expCoeff (fun n => 2 * pell n ^ (2 * k - 1)) 3 = z := by
  rintro ⟨z, hz⟩
  rw [expCoeff_three, pell_one, pell_two, pell_three] at hz
  set m := 2 * k - 1 with hm
  have h : (4 : ℤ) + 6 * 2 ^ m + 2 * 5 ^ m = 3 * z := by
    have : (((4 : ℤ) + 6 * 2 ^ m + 2 * 5 ^ m : ℤ) : ℚ) = ((3 * z : ℤ) : ℚ) := by
      push_cast; rw [← hz]; push_cast; ring
    exact_mod_cast this
  have hodd : Odd m := ⟨k - 1, by omega⟩
  have h3 := congrArg (fun x : ℤ => (x : ZMod 3)) h
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at h3
  have e5 : (5 : ZMod 3) = -1 := by decide
  have e6 : (6 : ZMod 3) = 0 := by decide
  have e3 : (3 : ZMod 3) = 0 := by decide
  rw [e5, e6, e3, hodd.neg_one_pow] at h3
  simp only [zero_mul, add_zero] at h3
  revert h3; decide

end OEIS_A208034

open OEIS_A208034 OEIS_A208034.Zs
