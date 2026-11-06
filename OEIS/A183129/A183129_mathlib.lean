import Mathlib
import OpenProblemsLib.DworkEuler

/-
OEIS A183129, A183128, A181084, A181082, A181080, A181078, A181076, A181074, A181070 (P. D. Hanna,
2010): A(x) = exp( Σ_{n≥1} [Σ_k B(n,k)^e(n,k) x^k] x^n/n ) with
  A181070: C(n,k), k ≤ n, e = k+1        A181074: C(n+k-1,k), e = k+1
  A181080: C(n,k), k ≤ n, e = n-k+1      A181076: C(n+k-1,k), e = n
  A181082: C(n,k), k ≤ n, e = n+k        A181078: C(n+k-1,k), e = n+k-1
  A181084: C(n,k), k ≤ n, e = n+k+1      A183128: C(n+k-1,k), e = k^2+1
                                         A183129: C(n+k-1,k), e = k^2+k
Each: "Conjecture: this sequence consists entirely of integers."

Definitions.
* `B1 n k = C(n,k)` (zero for k > n, so the restriction k ≤ n is automatic: every exponent above is
  ≥ 1 there), `B2 n k = C(n+k-1,k)`.
* `bf B e _ m = Σ_{n=1}^{m} (m/n) B(n, m-n)^e(n, m-n)` = m [x^m] of the logarithm above
  (the x^m coefficient of [Σ_k B(n,k)^e x^k] x^n/n is B(n,m-n)^e(n,m-n)/n).
* `A B e = recSeq (bf B e)`: a(0) = 1, (N+1) a(N+1) = Σ_{j=0..N} bf (j+1) a(N-j) (coefficients of
  exp); `bf` does not read `a`, so this is exp of a fixed series.

Main theorems: `A181070_int`, ..., `A183129_int : ∀ n, ∃ z : ℤ, a n = z` for the nine series.

Route (library `OpenProblemsLib.DworkEuler`, power families): with f = 1 + x (B1) or
f = 1 + x + ... + x^N (B2, truncated at the target degree N), B(n, m-n) = [x^m] (x f)^n
(`U_one_add_X`, `U_geom`), and (m/n) B^e = `Tpow f G m n` with G = e - 1 (G = 0 on the diagonal
k = 0, where B = 1). `gcond_of` turns two facts about e into the ray conditions of `Tpow_gauss`:
e(pn, pk) - 1 = e(n,k) - 1 + (p-1) L with p^t ∣ L whenever p^t ∣ n, k; and e(n,k) - 1 is at least
k (or n - k, or v_p(n)), which bounds the p-adic size needed when p divides B. Then the row sums
are Gauss sequences and `recSeq_int` gives integrality.
Not checked here: the recurrence as the OEIS "exp(...)" (standard reading); data agreement
(certificate/check.py).
-/

namespace A183129

open Polynomial OpenProblemsLib.Dwork OpenProblemsLib.DworkEuler

def B1 (n k : ℕ) : ℤ := (n.choose k : ℤ)

def B2 (n k : ℕ) : ℤ := ((n + k - 1).choose k : ℤ)

/-- `m [x^m] Σ_{n≥1} [Σ_k B(n,k)^e(n,k) x^k] x^n / n`. -/
noncomputable def bf (B : ℕ → ℕ → ℤ) (e : ℕ → ℕ → ℕ) (_g : ℕ → ℚ) (m : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 1 m, (m : ℚ) / n * (B n (m - n) : ℚ) ^ e n (m - n)

/-- Coefficients of `exp (Σ_{n≥1} [Σ_k B(n,k)^e(n,k) x^k] x^n / n)`. -/
noncomputable def A (B : ℕ → ℕ → ℤ) (e : ℕ → ℕ → ℕ) : ℕ → ℚ := recSeq (bf B e)

theorem fam_int (B : ℕ → ℕ → ℤ) (e : ℕ → ℕ → ℕ) (f : ℕ → Polynomial ℤ)
    (hf0 : ∀ N, (f N).coeff 0 = 1)
    (hU : ∀ N m n, 1 ≤ n → n ≤ m → m ≤ N → U (f N) m n = B n (m - n))
    (hB0 : ∀ n, 1 ≤ n → B n 0 = 1)
    (he : ∀ n k, 1 ≤ n → 1 ≤ k → 1 ≤ e n k)
    (hL : ∀ p : ℕ, p.Prime → ∀ n k, 1 ≤ n → 1 ≤ k → ∃ L,
      e (p * n) (p * k) - 1 = (e n k - 1) + (p - 1) * L ∧ ∀ t, p ^ t ∣ n → p ^ t ∣ k → p ^ t ∣ L)
    (hbig : ∀ p : ℕ, p.Prime → ∀ N n k, 1 ≤ n → 1 ≤ k → (p : ℤ) ∣ U (f N) (n + k) n →
      U (f N) (n + k) n ≠ 0 → min (n.factorization p) ((n + k).factorization p + 1) ≤ e n k - 1) :
    ∀ N, ∃ z : ℤ, A B e N = z := by
  apply recSeq_int (bf B e) (fun _ _ _ _ => rfl)
  intro gz N
  set G : ℕ → ℕ → ℕ := fun m n => if n = m then 0 else e n (m - n) - 1
  refine ⟨fun m => ∑ n ∈ Finset.range (m + 1), Tpow (f N) G m n, ?_, ?_⟩
  · intro p hp
    exact Tpow_gauss p hp (f N) G
      (gcond_of p hp (f N) (hf0 N) (fun n k => e n k - 1) (hL p hp) (hbig p hp N))
  · intro m hm1 hmN
    show bf B e _ m = ((∑ n ∈ Finset.range (m + 1), Tpow (f N) G m n : ℤ) : ℚ)
    rw [range_succ_eq_insert_Icc, Finset.sum_insert (by simp)]
    have h0 : Tpow (f N) G m 0 = 0 := by simp [Tpow, V]
    rw [h0, zero_add, bf]
    push_cast
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Tpow_cast, hU N m n hn.1 hn.2 hmN]
    by_cases hnm : n = m
    · subst hnm
      simp [G, hB0 n hn.1]
    · have : G m n + 1 = e n (m - n) := by
        have := he n (m - n) hn.1 (by omega)
        simp only [G, hnm, ↓reduceIte]; omega
      rw [this]

/-- Type 1 (`C(n,k)`, `f = 1 + x`). -/
theorem fam1_int (e : ℕ → ℕ → ℕ) (he : ∀ n k, 1 ≤ n → 1 ≤ k → 1 ≤ e n k)
    (hL : ∀ p : ℕ, p.Prime → ∀ n k, 1 ≤ n → 1 ≤ k → ∃ L,
      e (p * n) (p * k) - 1 = (e n k - 1) + (p - 1) * L ∧ ∀ t, p ^ t ∣ n → p ^ t ∣ k → p ^ t ∣ L)
    (hbig : ∀ p : ℕ, p.Prime → ∀ n k, 1 ≤ n → 1 ≤ k → (p : ℤ) ∣ (n.choose k : ℤ) →
      (n.choose k : ℤ) ≠ 0 → min (n.factorization p) ((n + k).factorization p + 1) ≤ e n k - 1) :
    ∀ N, ∃ z : ℤ, A B1 e N = z :=
  fam_int B1 e (fun _ => 1 + X) (fun _ => by simp)
    (fun _ m n _ h _ => U_one_add_X m n h) (fun n _ => by simp [B1]) he hL
    (fun p hp _ n k h1 h2 hU hU0 => by
      rw [U_one_add_X (n + k) n (by omega), Nat.add_sub_cancel_left] at hU hU0
      exact hbig p hp n k h1 h2 hU hU0)

/-- Type 2 (`C(n+k-1,k)`, `f = 1 + x + ... + x^N`). -/
theorem fam2_int (e : ℕ → ℕ → ℕ) (he : ∀ n k, 1 ≤ n → 1 ≤ k → 1 ≤ e n k)
    (hL : ∀ p : ℕ, p.Prime → ∀ n k, 1 ≤ n → 1 ≤ k → ∃ L,
      e (p * n) (p * k) - 1 = (e n k - 1) + (p - 1) * L ∧ ∀ t, p ^ t ∣ n → p ^ t ∣ k → p ^ t ∣ L)
    (hbig : ∀ p : ℕ, p.Prime → ∀ n k, 1 ≤ n → 1 ≤ k →
      min (n.factorization p) ((n + k).factorization p + 1) ≤ e n k - 1) :
    ∀ N, ∃ z : ℤ, A B2 e N = z :=
  fam_int B2 e geomTrunc
    (fun N => by
      rw [geomTrunc, PowerSeries.coeff_trunc]; simp)
    (fun N m n h1 h hm => by
      rw [U_geom N m n h1 h hm, B2, show n + (m - n) - 1 = m - 1 by omega])
    (fun n _ => by simp [B2]) he hL
    (fun p hp _ n k h1 h2 _ _ => hbig p hp n k h1 h2)

/-! ## The exponent facts -/

theorem scale (p a : ℕ) (hp : 1 ≤ p) : p * a = a + (p - 1) * a := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]; ring

theorem big_k (p : ℕ) (hp : p.Prime) (n k g : ℕ) (hk : 1 ≤ k) (hkg : k ≤ g) :
    min (n.factorization p) ((n + k).factorization p + 1) ≤ g := by
  apply big_of_dvd p hp (n + k) n k g hk _ hkg
  have h1 : p ^ min ((n + k).factorization p) (n.factorization p) ∣ n + k :=
    (pow_dvd_pow p (min_le_left _ _)).trans (Nat.ordProj_dvd _ p)
  have h2 : p ^ min ((n + k).factorization p) (n.factorization p) ∣ n :=
    (pow_dvd_pow p (min_le_right _ _)).trans (Nat.ordProj_dvd _ p)
  have := Nat.dvd_sub h1 h2
  rwa [Nat.add_sub_cancel_left] at this

theorem big_n (p : ℕ) (hp : p.Prime) (n k g : ℕ) (hn : 1 ≤ n) (hng : n - 1 ≤ g) :
    min (n.factorization p) ((n + k).factorization p + 1) ≤ g := by
  apply big_of_vp
  have := vp_lt p hp n (by omega)
  omega

/-! ## The nine series -/

/-- A181070: C(n,k)^(k+1). -/
noncomputable def a181070 : ℕ → ℚ := A B1 (fun _ k => k + 1)
/-- A181080: C(n,k)^(n-k+1). -/
noncomputable def a181080 : ℕ → ℚ := A B1 (fun n k => n - k + 1)
/-- A181082: C(n,k)^(n+k). -/
noncomputable def a181082 : ℕ → ℚ := A B1 (fun n k => n + k)
/-- A181084: C(n,k)^(n+k+1). -/
noncomputable def a181084 : ℕ → ℚ := A B1 (fun n k => n + k + 1)
/-- A181074: C(n+k-1,k)^(k+1). -/
noncomputable def a181074 : ℕ → ℚ := A B2 (fun _ k => k + 1)
/-- A181076: C(n+k-1,k)^n. -/
noncomputable def a181076 : ℕ → ℚ := A B2 (fun n _ => n)
/-- A181078: C(n+k-1,k)^(n+k-1). -/
noncomputable def a181078 : ℕ → ℚ := A B2 (fun n k => n + k - 1)
/-- A183128: C(n+k-1,k)^(k^2+1). -/
noncomputable def a183128 : ℕ → ℚ := A B2 (fun _ k => k ^ 2 + 1)
/-- A183129: C(n+k-1,k)^(k^2+k). -/
noncomputable def a183129 : ℕ → ℚ := A B2 (fun _ k => k ^ 2 + k)

theorem A181070_int (N : ℕ) : ∃ z : ℤ, a181070 N = z :=
  fam1_int _ (fun _ _ _ _ => by omega)
    (fun p hp n k _ _ => ⟨k, by simp only [Nat.add_sub_cancel]; exact scale p k hp.one_lt.le,
      fun _ _ h => h⟩)
    (fun p hp n k _ hk _ _ => big_k p hp n k _ hk (by omega)) N

theorem A181074_int (N : ℕ) : ∃ z : ℤ, a181074 N = z :=
  fam2_int _ (fun _ _ _ _ => by omega)
    (fun p hp n k _ _ => ⟨k, by simp only [Nat.add_sub_cancel]; exact scale p k hp.one_lt.le,
      fun _ _ h => h⟩)
    (fun p hp n k _ hk => big_k p hp n k _ hk (by omega)) N

theorem A181082_int (N : ℕ) : ∃ z : ℤ, a181082 N = z :=
  fam1_int _ (fun _ _ _ _ => by omega)
    (fun p hp n k hn _ => ⟨n + k, by
      have h1 := scale p (n + k) hp.one_lt.le
      have h2 : p * n + p * k = p * (n + k) := by ring
      omega, fun _ h1 h2 => Nat.dvd_add h1 h2⟩)
    (fun p hp n k hn _ _ _ => big_n p hp n k _ hn (by omega)) N

theorem A181084_int (N : ℕ) : ∃ z : ℤ, a181084 N = z :=
  fam1_int _ (fun _ _ _ _ => by omega)
    (fun p hp n k hn _ => ⟨n + k, by
      have h1 := scale p (n + k) hp.one_lt.le
      have h2 : p * n + p * k = p * (n + k) := by ring
      omega, fun _ h1 h2 => Nat.dvd_add h1 h2⟩)
    (fun p hp n k hn _ _ _ => big_n p hp n k _ hn (by omega)) N

theorem A181076_int (N : ℕ) : ∃ z : ℤ, a181076 N = z :=
  fam2_int _ (fun _ _ hn _ => hn)
    (fun p hp n k hn _ => ⟨n, by
      have h1 := scale p n hp.one_lt.le
      have h2 : n ≤ p * n := Nat.le_mul_of_pos_left n hp.pos
      omega, fun _ h1 _ => h1⟩)
    (fun p hp n k hn _ => big_n p hp n k _ hn le_rfl) N

theorem A181078_int (N : ℕ) : ∃ z : ℤ, a181078 N = z :=
  fam2_int _ (fun _ _ _ _ => by omega)
    (fun p hp n k hn hk => ⟨n + k, by
      have h1 := scale p (n + k) hp.one_lt.le
      have h2 : p * n + p * k = p * (n + k) := by ring
      omega, fun _ h1 h2 => Nat.dvd_add h1 h2⟩)
    (fun p hp n k hn hk => big_n p hp n k _ hn (by omega)) N

theorem A181080_int (N : ℕ) : ∃ z : ℤ, a181080 N = z :=
  fam1_int _ (fun _ _ _ _ => by omega)
    (fun p hp n k _ _ => ⟨n - k, by
      have h1 := scale p (n - k) hp.one_lt.le
      have h2 : p * n - p * k = p * (n - k) := (Nat.mul_sub p n k).symm
      omega, fun _ h1 h2 => Nat.dvd_sub h1 h2⟩)
    (fun p hp n k hn hk hU hU0 => by
      have hkn : k < n := by
        rcases Nat.lt_trichotomy k n with h | h | h
        · exact h
        · subst h
          rw [Nat.choose_self, Nat.cast_one] at hU
          exact absurd (Int.eq_one_of_dvd_one (by positivity) hU)
            (by exact_mod_cast hp.one_lt.ne')
        · exact absurd (by rw [Nat.choose_eq_zero_of_lt h]; simp) hU0
      apply big_of_dvd p hp (n + k) n (n - k) _ (by omega) _ (by omega)
      have h1 : p ^ min ((n + k).factorization p) (n.factorization p) ∣ n + k :=
        (pow_dvd_pow p (min_le_left _ _)).trans (Nat.ordProj_dvd _ p)
      have h2 : p ^ min ((n + k).factorization p) (n.factorization p) ∣ n :=
        (pow_dvd_pow p (min_le_right _ _)).trans (Nat.ordProj_dvd _ p)
      have h3 := Nat.dvd_sub h1 h2
      rw [Nat.add_sub_cancel_left] at h3
      exact Nat.dvd_sub h2 h3) N

theorem A183128_int (N : ℕ) : ∃ z : ℤ, a183128 N = z :=
  fam2_int _ (fun _ _ _ _ => by omega)
    (fun p hp n k _ _ => ⟨(p + 1) * k ^ 2, by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
      simp only [Nat.add_sub_cancel]; ring,
      fun _ _ h => Dvd.dvd.mul_left (h.trans (Dvd.intro_left _ (pow_two k).symm)) _⟩)
    (fun p hp n k _ hk => big_k p hp n k _ hk
      (by have h : k ≤ k ^ 2 := Nat.le_self_pow (by norm_num) k; omega)) N

theorem A183129_int (N : ℕ) : ∃ z : ℤ, a183129 N = z :=
  fam2_int _ (fun _ _ _ hk => by nlinarith)
    (fun p hp n k _ hk => ⟨(p + 1) * k ^ 2 + k, by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
      have e1 : ((q + 1) * k) ^ 2 + (q + 1) * k = (k ^ 2 + k) + q * ((q + 1 + 1) * k ^ 2 + k) := by
        ring
      have e2 : 1 ≤ k ^ 2 + k := by nlinarith
      simp only [Nat.add_sub_cancel]
      omega,
      fun _ _ h => Nat.dvd_add (Dvd.dvd.mul_left (h.trans (Dvd.intro_left _ (pow_two k).symm)) _)
        h⟩)
    (fun p hp n k _ hk => big_k p hp n k _ hk
      (by have h : k ≤ k ^ 2 := Nat.le_self_pow (by norm_num) k; omega)) N
