import Mathlib

/-
OEIS A207969, A207970 (P. D. Hanna, 2012): g.f. exp(Σ_{n≥1} 5 F(n)^4 x^n/n) and
exp(Σ_{n≥1} 5 F(n)^6 x^n/n). Conjecture (both entries): exp(Σ_{n≥1} 5 F(n)^(2k) x^n/n)
is an integer series for every integer k ≥ 0.

Definitions.
* `bseq k n = 5 * Nat.fib n ^ (2k)`.
* `expCoeff b n`: coefficients of exp(Σ b(n) x^n/n), given by A(0) = 1 and
  (n+1) A(n+1) = Σ_{j=0..n} b(j+1) A(n-j) (equivalently x A' = (Σ b(n) x^n) A), over ℚ.

Main theorem.
* `A207969_conjecture k n : ∃ z : ℤ, expCoeff (bseq k) n = z`
  (`A207969_int`, `A207970_int`: k = 2, 3).

Route.
* `Zphi`: the ring ℤ[φ]; `phi_pow` (φ^n = (F(n+1) - F(n)) + F(n) φ), trace `tr`, norm `N`,
  conjugation `sig`. `frob`: for p prime, p ≠ 5, z^p ≡ τ z (mod p) with τ = id or sig
  (via (2φ - 1)^2 = 5 and 5^((p-1)/2) ≡ ±1). `lucas_gauss`: with
  `dvd_sub_pow_of_dvd_sub`, L(m p^a) ≡ L(m p^(a-1)) (mod p^a) for L(n) = tr(φ^n).
* `five_fib_sq`: 5 F(n)^2 = L(2n) - 2(-1)^n; `LGp_*`: the congruence
  b(m p^a) ≡ b(m p^(a-1)) (mod p^a) is closed under products, differences, scalars;
  dividing (5F^2)^k = 5^(k-1) b by 5^(k-1) is allowed for p ≠ 5. For p = 5,
  `five_pow_dvd_fib` (5^j | n ⇒ 5^j | F(n), from F(5m) = 5 F(m) q) gives
  5^a | b(m 5^a) and 5^a | b(m 5^(a-1)) directly (`LG_bseq`).
* `dwork`: these congruences give integers c(d) with b(n) = Σ_{d|n} d c(d).
* `expCoeff_int_of_euler`: then exp(Σ b x^n/n) = Π_d (1 - x^d)^(-c(d)); the truncated
  product `EP` lies in ℤ⟦X⟧, satisfies θ EP = EB · EP (θ = x d/dx, `LD_EP`), and `EB`
  agrees with Σ b(n) x^n up to degree D (`coeff_EB`), so its coefficients equal expCoeff
  (`expCoeff_eq`).
Checked: all of the above, for all k and n. Not checked: that `expCoeff` is the OEIS
"exp(...)" (the recurrence is the standard characterisation, stated above); the data
match is checked by certificate/check.py only. Axioms: propext, Classical.choice, Quot.sound.
-/

namespace OEIS_A207969

/-- `ℤ[φ]`, φ² = φ + 1: the pair `⟨a, b⟩` is `a + b φ`. -/
@[ext] structure Zphi where
  a : ℤ
  b : ℤ

namespace Zphi

instance : Add Zphi := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Mul Zphi := ⟨fun x y => ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩⟩
instance : Neg Zphi := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub Zphi := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
instance : Zero Zphi := ⟨⟨0, 0⟩⟩
instance : One Zphi := ⟨⟨1, 0⟩⟩

@[simp] theorem add_a (x y : Zphi) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : Zphi) : (x + y).b = x.b + y.b := rfl
@[simp] theorem mul_a (x y : Zphi) : (x * y).a = x.a * y.a + x.b * y.b := rfl
@[simp] theorem mul_b (x y : Zphi) : (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl
@[simp] theorem neg_a (x : Zphi) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : Zphi) : (-x).b = -x.b := rfl
@[simp] theorem sub_a (x y : Zphi) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : Zphi) : (x - y).b = x.b - y.b := rfl
@[simp] theorem zero_a : (0 : Zphi).a = 0 := rfl
@[simp] theorem zero_b : (0 : Zphi).b = 0 := rfl
@[simp] theorem one_a : (1 : Zphi).a = 1 := rfl
@[simp] theorem one_b : (1 : Zphi).b = 0 := rfl

instance : CommRing Zphi where
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

theorem natCast_eq (n : ℕ) : (n : Zphi) = ⟨n, 0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.cast_succ, ih]; ext <;> simp

theorem intCast_eq (n : ℤ) : (n : Zphi) = ⟨n, 0⟩ := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simp [natCast_eq]
  · rw [Int.cast_neg, Int.cast_natCast, natCast_eq]; ext <;> simp

theorem dvd_iff (q : ℤ) (z : Zphi) : (q : Zphi) ∣ z ↔ q ∣ z.a ∧ q ∣ z.b := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [intCast_eq]
    exact ⟨⟨w.a, by simp⟩, ⟨w.b, by simp⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    refine ⟨⟨u, v⟩, ?_⟩
    rw [intCast_eq]; ext <;> simp [hu, hv]

def phi : Zphi := ⟨0, 1⟩

theorem phi_pow (n : ℕ) : phi ^ n = ⟨(Nat.fib (n + 1) : ℤ) - Nat.fib n, Nat.fib n⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    have h := Nat.fib_add_two (n := n)
    have h' : (Nat.fib (n + 1 + 1) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by exact_mod_cast h
    ext
    · simp [phi, h']
    · simp [phi]

/-- conjugation φ ↦ 1 - φ -/
def sig : Zphi →+* Zphi where
  toFun x := ⟨x.a + x.b, -x.b⟩
  map_one' := by ext <;> simp
  map_mul' := by intros; ext <;> simp <;> ring
  map_zero' := by ext <;> simp
  map_add' := by intros; ext <;> simp <;> ring

def tr (x : Zphi) : ℤ := 2 * x.a + x.b

theorem tr_sig (x : Zphi) : tr (sig x) = tr x := by simp [tr, sig]; ring

theorem tr_sub (x y : Zphi) : tr (x - y) = tr x - tr y := by simp [tr]; ring

theorem dvd_tr (q : ℤ) (z : Zphi) (h : (q : Zphi) ∣ z) : q ∣ tr z := by
  rw [dvd_iff] at h
  exact dvd_add (dvd_mul_of_dvd_right h.1 _) h.2

/-- Lucas numbers as traces -/
def L (n : ℕ) : ℤ := tr (phi ^ n)

theorem fermat_int (p : ℕ) (hp : p.Prime) (x : ℤ) : (p : ℤ) ∣ x ^ p - x := by
  have := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.pow_card, sub_self]

theorem decomp (z : Zphi) : z = (z.a : Zphi) + (z.b : Zphi) * phi := by
  ext <;> simp [intCast_eq, phi]

theorem int_dvd_cast (q x : ℤ) (h : q ∣ x) : (q : Zphi) ∣ (x : Zphi) := by
  obtain ⟨w, rfl⟩ := h; exact ⟨w, by push_cast; ring⟩

theorem dvd_of_two_mul (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (X : Zphi)
    (h : (p : Zphi) ∣ ((2 : ℤ) : Zphi) * X) : (p : Zphi) ∣ X := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hn2 : ¬ (p : ℤ) ∣ 2 := by
    intro h'
    have : p ∣ 2 := by exact_mod_cast h'
    rcases (Nat.prime_two.eq_one_or_self_of_dvd p this) with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact h2 h1
  rw [show ((p : ℕ) : Zphi) = ((p : ℤ) : Zphi) by push_cast; rfl, dvd_iff] at h ⊢
  rw [intCast_eq] at h
  simp only [mul_a, mul_b, zero_mul, add_zero] at h
  exact ⟨(hpz.dvd_or_dvd h.1).resolve_left hn2, (hpz.dvd_or_dvd (by simpa using h.2)).resolve_left hn2⟩

/-- Frobenius: for p prime, p ≠ 5, there is τ ∈ {id, σ} with z^p ≡ τ z (mod p). -/
theorem frob (p : ℕ) (hp : p.Prime) (h5 : p ≠ 5) :
    ∃ τ : Zphi →+* Zphi, (∀ x, tr (τ x) = tr x) ∧ ∀ z : Zphi, (p : Zphi) ∣ z ^ p - τ z := by
  -- first the generator
  have hphi : ∃ τ : Zphi →+* Zphi, (∀ x, tr (τ x) = tr x) ∧ (p : Zphi) ∣ phi ^ p - τ phi := by
    rcases hp.eq_two_or_odd' with rfl | hodd
    · refine ⟨sig, tr_sig, ⟨phi, ?_⟩⟩
      rw [natCast_eq]; ext <;> simp [phi, sig, pow_two]
    · obtain ⟨j, hj⟩ := hodd
      set s : Zphi := ⟨-1, 2⟩ with hs
      have hs2 : s ^ 2 = ((5 : ℤ) : Zphi) := by rw [intCast_eq, hs]; ext <;> simp [pow_two]
      have h2phi : 1 + s = ((2 : ℤ) : Zphi) * phi := by rw [intCast_eq, hs]; ext <;> simp [phi]
      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (1 : Zphi) s
      rw [h2phi, mul_pow, one_pow] at hr
      -- 2^p = 2 + p w
      obtain ⟨w, hw⟩ := fermat_int p hp 2
      have hw' : ((2 : ℤ) : Zphi) ^ p = ((2 : ℤ) : Zphi) + (p : Zphi) * (w : Zphi) := by
        rw [← Int.cast_pow, show (2 : ℤ) ^ p = 2 + p * w by linarith]; push_cast; ring
      -- 5^j = ε + p t
      have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      have h5p : (p : ℤ) ∣ 5 ^ (2 * j) - 1 := by
        have h := fermat_int p hp 5
        have e5 : (5 : ℤ) ^ p - 5 = 5 * (5 ^ (2 * j) - 1) := by rw [hj]; ring
        rw [e5] at h
        rcases hpz.dvd_or_dvd h with h' | h'
        · exfalso
          have : (p : ℤ) ≤ 5 := Int.le_of_dvd (by norm_num) h'
          have h55 : p ∣ 5 := by exact_mod_cast h'
          rcases (Nat.prime_five.eq_one_or_self_of_dvd p h55) with h1 | h1
          · exact hp.one_lt.ne' h1
          · exact h5 h1
        · exact h'
      have hfac : (5 : ℤ) ^ (2 * j) - 1 = (5 ^ j - 1) * (5 ^ j + 1) := by ring
      rw [hfac] at h5p
      have hsp : s ^ p = s * ((5 ^ j : ℤ) : Zphi) := by
        rw [hj, pow_succ, pow_mul, hs2]; push_cast; ring
      rcases hpz.dvd_or_dvd h5p with ⟨t, ht⟩ | ⟨t, ht⟩
      · -- ε = 1, τ = id
        refine ⟨RingHom.id _, fun _ => rfl, ?_⟩
        have he : ((5 ^ j : ℤ) : Zphi) = 1 + (p : Zphi) * (t : Zphi) := by
          rw [show (5 : ℤ) ^ j = 1 + p * t by linarith]; push_cast; ring
        have key : ((2 : ℤ) : Zphi) * (phi ^ p - phi) =
            (p : Zphi) * (s * t + s * r - (w : Zphi) * phi ^ p) := by
          linear_combination hr - phi ^ p * hw' + hsp + s * he + h2phi
        exact dvd_of_two_mul p hp (by omega) _ ⟨_, key⟩
      · -- ε = -1, τ = σ
        refine ⟨sig, tr_sig, ?_⟩
        have he : ((5 ^ j : ℤ) : Zphi) = -1 + (p : Zphi) * (t : Zphi) := by
          rw [show (5 : ℤ) ^ j = -1 + p * t by linarith]; push_cast; ring
        have hsig : 1 - s = ((2 : ℤ) : Zphi) * sig phi := by
          rw [intCast_eq, hs]; ext <;> simp [phi, sig]
        have key : ((2 : ℤ) : Zphi) * (phi ^ p - sig phi) =
            (p : Zphi) * (s * t + s * r - (w : Zphi) * phi ^ p) := by
          linear_combination hr - phi ^ p * hw' + hsp + s * he + hsig
        exact dvd_of_two_mul p hp (by omega) _ ⟨_, key⟩
  obtain ⟨τ, htr, hτ⟩ := hphi
  refine ⟨τ, htr, fun z => ?_⟩
  obtain ⟨A, B⟩ := z
  have hz : (⟨A, B⟩ : Zphi) = (A : Zphi) + (B : Zphi) * phi := decomp _
  rw [hz]
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (A : Zphi) ((B : Zphi) * phi)
  have eq : ((A : Zphi) + (B : Zphi) * phi) ^ p - τ ((A : Zphi) + (B : Zphi) * phi) =
      ((A ^ p - A : ℤ) : Zphi) + ((B ^ p - B : ℤ) : Zphi) * phi ^ p +
      (B : Zphi) * (phi ^ p - τ phi) + (p : Zphi) * ((A : Zphi) * ((B : Zphi) * phi) * r) := by
    rw [hr]; simp only [map_add, map_mul, map_intCast]; push_cast; ring
  rw [eq]
  refine dvd_add (dvd_add (dvd_add ?_ ?_) ?_) (dvd_mul_right _ _)
  · exact int_dvd_cast _ _ (fermat_int p hp _)
  · exact dvd_mul_of_dvd_left (int_dvd_cast _ _ (fermat_int p hp _)) _
  · exact dvd_mul_of_dvd_right hτ _


theorem lucas_gauss (p : ℕ) (hp : p.Prime) (h5 : p ≠ 5) (a m : ℕ) (ha : 1 ≤ a) :
    ((p : ℤ) ^ a) ∣ L (m * p ^ a) - L (m * p ^ (a - 1)) := by
  obtain ⟨τ, htr, hτ⟩ := frob p hp h5
  have h := dvd_sub_pow_of_dvd_sub (hτ (phi ^ m)) (a - 1)
  rw [show a - 1 + 1 = a by omega] at h
  have e1 : ((phi ^ m) ^ p) ^ p ^ (a - 1) = phi ^ (m * p ^ a) := by
    rw [← pow_mul, ← pow_mul, show p * p ^ (a - 1) = p ^ a by
      rw [← pow_succ']; congr 1; omega]
  have e2 : (τ (phi ^ m)) ^ p ^ (a - 1) = τ (phi ^ (m * p ^ (a - 1))) := by
    rw [← map_pow, ← pow_mul]
  rw [e1, e2] at h
  have := dvd_tr ((p : ℤ) ^ a) _ (by push_cast; exact h)
  rw [tr_sub, htr] at this
  exact this

/-- norm -/
def N (x : Zphi) : ℤ := x.a ^ 2 + x.a * x.b - x.b ^ 2

theorem N_mul (x y : Zphi) : N (x * y) = N x * N y := by simp [N]; ring

theorem N_phi_pow (n : ℕ) : N (phi ^ n) = (-1) ^ n := by
  induction n with
  | zero => simp [N]
  | succ n ih => rw [pow_succ, N_mul, ih, pow_succ]; simp [N, phi]

theorem five_fib_sq (n : ℕ) : 5 * (Nat.fib n : ℤ) ^ 2 = L (2 * n) - 2 * (-1) ^ n := by
  rw [← N_phi_pow, L, pow_mul', phi_pow]
  simp [N, tr, pow_two]; ring

theorem fib_five_mul (m : ℕ) : ∃ q : ℤ, (Nat.fib (5 * m) : ℤ) = 5 * Nat.fib m * q := by
  have h := phi_pow (5 * m)
  rw [pow_mul', phi_pow] at h
  set x : ℤ := (Nat.fib (m + 1) : ℤ) - Nat.fib m
  set y : ℤ := (Nat.fib m : ℤ)
  refine ⟨x ^ 4 + 2 * x ^ 3 * y + 4 * x ^ 2 * y ^ 2 + 3 * x * y ^ 3 + y ^ 4, ?_⟩
  have hb := congrArg Zphi.b h
  simp only [pow_succ, pow_zero, one_mul, mul_b, mul_a] at hb
  rw [← hb]; ring

theorem five_pow_dvd_fib (j m : ℕ) : (5 : ℤ) ^ j ∣ Nat.fib (5 ^ j * m) := by
  induction j generalizing m with
  | zero => simp
  | succ j ih =>
    obtain ⟨q, hq⟩ := fib_five_mul (5 ^ j * m)
    rw [show 5 ^ (j + 1) * m = 5 * (5 ^ j * m) by ring, hq, pow_succ]
    obtain ⟨w, hw⟩ := ih m
    rw [hw]; exact ⟨w * q, by ring⟩

end Zphi

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

/-! ## the sequence 5 F(n)^(2k) -/

open Zphi

/-- `b n = 5 * Fibonacci(n)^(2k)` -/
def bseq (k n : ℕ) : ℤ := 5 * (Nat.fib n : ℤ) ^ (2 * k)

theorem five_pow_dvd_bseq (k a N : ℕ) (hk : 1 ≤ k) (h : (5 : ℤ) ^ (a - 1) ∣ Nat.fib N) :
    (5 : ℤ) ^ a ∣ bseq k N := by
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
  by_cases h5 : p = 5
  · subst h5
    intro a m ha
    apply dvd_sub
    · apply five_pow_dvd_bseq k a _ hk
      have := five_pow_dvd_fib a m
      rw [mul_comm m] 
      exact (pow_dvd_pow 5 (by omega)).trans this
    · apply five_pow_dvd_bseq k a _ hk
      rw [mul_comm m]
      exact five_pow_dvd_fib (a - 1) m
  · -- s n = 5 F_n^2 = L(2n) - 2(-1)^n satisfies the congruence at p
    have hL : LGp p (fun n => L (2 * n)) := by
      intro a m ha
      have := lucas_gauss p hp h5 a (2 * m) ha
      simp only; rw [← mul_assoc, ← mul_assoc]; exact this
    have hs : LGp p (fun n => 5 * (Nat.fib n : ℤ) ^ 2) := by
      have := LGp_sub hL (LGp_const_mul (LGp_neg_one p hp) 2)
      have e : (fun n => 5 * (Nat.fib n : ℤ) ^ 2) = (fun n => L (2 * n) - 2 * (-1) ^ n) := by
        funext n; exact five_fib_sq n
      rw [e]; exact this
    have hsk := LGp_pow hs k
    intro a m ha
    have h1 := hsk a m ha
    have e : ∀ N, (5 * (Nat.fib N : ℤ) ^ 2) ^ k = 5 ^ (k - 1) * bseq k N := by
      intro N; unfold bseq
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hk]
    simp only [e] at h1
    rw [← mul_sub] at h1
    have hcop : IsCoprime ((p : ℤ) ^ a) ((5 : ℤ) ^ (k - 1)) := by
      apply IsCoprime.pow
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime p 5 := (Nat.coprime_primes hp Nat.prime_five).mpr h5
      show Int.gcd (p : ℤ) ((5 : ℕ) : ℤ) = 1
      rw [Int.gcd_natCast_natCast]; exact this
    exact hcop.dvd_of_dvd_mul_left h1

/-- Conjecture of A207969 / A207970 (Hanna): `exp (∑_{n ≥ 1} 5 F(n)^(2k) x^n / n)` has integer
coefficients for every `k ≥ 0`. -/
theorem A207969_conjecture (k n : ℕ) : ∃ z : ℤ, expCoeff (bseq k) n = z :=
  expCoeff_int_of_euler (bseq k) (cOf (bseq k)) (dwork _ (LG_bseq k)) n

/-- A207969 is the case k = 2 and A207970 the case k = 3. -/
theorem A207969_int (n : ℕ) : ∃ z : ℤ, expCoeff (bseq 2) n = z := A207969_conjecture 2 n

theorem A207970_int (n : ℕ) : ∃ z : ℤ, expCoeff (bseq 3) n = z := A207969_conjecture 3 n

end OEIS_A207969

open OEIS_A207969 OEIS_A207969.Zphi
