import Mathlib

/-
OEIS-A192062 (Mathlib). Column j of T (A192062): T(0)=0, T(1)=1, T(2i)=T(2i-2)+T(2i-1),
T(2i+1)=T(2i-1)+j T(2i). Column j of A (A191971): A(0)=2, A(1)=1, A(2i)=j A(2i-1)+A(2i-2),
A(2i+1)=A(2i)+A(2i-1). With p_0 = 2, p_1 = 3, ... (`Nat.nth Nat.Prime`), `Gchain j 0 = T` and
`Gchain j (k+1) n = Gchain j k (p_k n) / Gchain j k n` (natural division). README's G_{k+1} is
`Gchain j k` here (G_1 = T, G_2 = A, G_3 = B, ...).

Main theorems.
- `A192062_main`: for all j, k and n ≥ 1, Gchain j k n ≥ 1, it divides Gchain j k (p_k n), and
  Gchain j k (p_k n) = Gchain j k n * Gchain j (k+1) n (Ramsey's conjecture: the chain continues
  for every prime, with integer factors).
- `A192062_G1`: Gchain j 1 n = A j n for n ≥ 1, i.e. T(2n) = A(n) T(n) (`T_double`).

Proof (differs from the README's cyclotomic route). T is a strong divisibility sequence,
gcd(T a, T b) = T(gcd a b) (`T_gcd`, from the addition formula `T_add`, consecutive terms
coprime, and T(odd) coprime to j). For any strong divisibility sequence F of positive terms and
any prime ℓ, f(m) = v_ℓ(F m) satisfies f(gcd a b) = min(f a, f b). The k-th iterated quotient has
v_ℓ equal to the k-th iterated difference g_k of f (`Gq_spec`), and g_k ≥ 0 for every such f
(`g_nonneg`): with f'(m) = f(p_k m) and c = f(n p_0...p_(k-1)), f(n d) = min(f'(n d), c) for
d ∣ p_0...p_(k-1), so g_(k+1)(n) = g_k[f'](n) - g_k[min(f', c)](n) = g_k[max(f' - c, 0)](n) ≥ 0
by induction (max(f' - c, 0) is again gcd-to-min).

Outside Lean: none.
-/

open Finset

/-! ## The sequences -/

def T (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => T j n + (if n % 2 = 0 then 1 else j) * T j (n + 1)

def A (j : ℕ) : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => A j n + (if n % 2 = 0 then j else 1) * A j (n + 1)

lemma T_two (j n : ℕ) : T j (n + 2) = T j n + (if n % 2 = 0 then 1 else j) * T j (n + 1) := rfl

/-- Addition formula. -/
theorem T_add (j n : ℕ) : ∀ m, T j (m + n + 1) =
    (if m % 2 = 1 ∧ n % 2 = 1 then j else 1) * T j (m + 1) * T j (n + 1) +
    (if m % 2 = 0 ∧ n % 2 = 0 then j else 1) * T j m * T j n
  | 0 => by simp [T]
  | 1 => by
    rw [show 1 + n + 1 = n + 2 by omega, T_two]
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp [hn, T] <;> ring
  | m + 2 => by
    have h0 := T_add j n m
    have h1 := T_add j n (m + 1)
    have e1 : T j (m + 2 + n + 1) = T j (m + n + 1) +
        (if (m + n + 1) % 2 = 0 then 1 else j) * T j (m + 1 + n + 1) := by
      rw [show m + 2 + n + 1 = (m + n + 1) + 2 by omega,
        show m + 1 + n + 1 = (m + n + 1) + 1 by omega, T_two]
    have t1 : T j (m + 1 + 1) = T j (m + 2) := rfl
    rw [e1, h0, h1, T_two j (m + 1), t1, T_two j m]
    have q1 : (m + 2) % 2 = m % 2 := by omega
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    all_goals
      have q2 : (m + 1) % 2 = 1 - m % 2 := by omega
      have q3 : (m + n + 1) % 2 = (1 + m % 2 + n % 2) % 2 := by omega
      simp only [q1, q2, q3, hm, hn] at *
      norm_num
      ring

lemma T_pos (j : ℕ) : ∀ n, 0 < n → 0 < T j n
  | 0, h => absurd h (lt_irrefl 0)
  | 1, _ => by simp [T]
  | n + 2, _ => by
    rw [T_two]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [T]
    · have := T_pos j n hn; omega

lemma T_cop_succ (j : ℕ) : ∀ n, Nat.Coprime (T j n) (T j (n + 1))
  | 0 => by simp [T]
  | n + 1 => by
    unfold Nat.Coprime
    rw [T_two, Nat.gcd_add_mul_right_right, Nat.gcd_comm]
    exact T_cop_succ j n

lemma T_odd_cop (j : ℕ) : ∀ n, n % 2 = 1 → Nat.Coprime (T j n) j
  | 0, h => by simp at h
  | 1, _ => by simp [T]
  | n + 2, h => by
    rw [T_two]
    simp only [eq_false (show ¬ n % 2 = 0 by omega), ↓reduceIte]
    rw [Nat.coprime_add_mul_left_left]
    exact T_odd_cop j n (by omega)

/-- gcd(T(m + n), T n) = gcd(T m, T n). -/
lemma T_gcd_step (j m n : ℕ) : Nat.gcd (T j (m + n)) (T j n) = Nat.gcd (T j m) (T j n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [T]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [← add_assoc, T_add]
  have hc : Nat.Coprime ((if m % 2 = 0 ∧ n' % 2 = 0 then j else 1) * T j n') (T j (n' + 1)) := by
    refine Nat.coprime_mul_iff_left.2 ⟨?_, T_cop_succ j n'⟩
    split_ifs with h
    · exact (T_odd_cop j (n' + 1) (by omega)).symm
    · exact Nat.coprime_one_left _
  have e : (if m % 2 = 1 ∧ n' % 2 = 1 then j else 1) * T j (m + 1) * T j (n' + 1) +
      (if m % 2 = 0 ∧ n' % 2 = 0 then j else 1) * T j m * T j n' =
      (if m % 2 = 0 ∧ n' % 2 = 0 then j else 1) * T j n' * T j m +
        ((if m % 2 = 1 ∧ n' % 2 = 1 then j else 1) * T j (m + 1)) * T j (n' + 1) := by ring
  rw [e, Nat.gcd_add_mul_right_left, Nat.Coprime.gcd_mul_left_cancel _ hc]

lemma T_gcd_mod (j r a : ℕ) : ∀ q, Nat.gcd (T j (r + a * q)) (T j a) = Nat.gcd (T j r) (T j a)
  | 0 => by simp
  | q + 1 => by
    rw [show r + a * (q + 1) = (r + a * q) + a by ring, T_gcd_step]
    exact T_gcd_mod j r a q

/-- T is a strong divisibility sequence. -/
theorem T_gcd (j a b : ℕ) : Nat.gcd (T j a) (T j b) = T j (Nat.gcd a b) := by
  induction a, b using Nat.gcd.induction with
  | H0 b => simp [T]
  | H1 a b ha ih =>
    rw [Nat.gcd_rec a b, ← ih, Nat.gcd_comm, ← T_gcd_mod j (b % a) a (b / a), Nat.mod_add_div]

lemma A_eq (j : ℕ) : ∀ n, A j (n + 1) = T j (n + 2) + T j n
  | 0 => by simp [A, T]
  | 1 => by simp [A, T]; ring
  | n + 2 => by
    have h0 := A_eq j n
    have h1 := A_eq j (n + 1)
    show A j (n + 1) + _ * A j (n + 2) = _
    rw [h0, h1, show n + 2 + 2 = (n + 2) + 2 by rfl, T_two (n := n + 2), T_two (n := n + 1),
      T_two (n := n)]
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    all_goals
      have q1 : (n + 1) % 2 = 1 - n % 2 := by omega
      have q2 : (n + 2) % 2 = n % 2 := by omega
      simp only [q1, q2, hn]
      norm_num
      ring

/-- T(2n) = A(n) T(n). -/
theorem T_double (j n : ℕ) : T j (2 * n) = A j n * T j n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [T]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (n' + 1) = (n' + 1) + n' + 1 by ring, T_add, A_eq]
  have c1 : ¬ ((n' + 1) % 2 = 1 ∧ n' % 2 = 1) := by omega
  have c2 : ¬ ((n' + 1) % 2 = 0 ∧ n' % 2 = 0) := by omega
  simp only [eq_false c1, eq_false c2, ↓reduceIte]
  ring

/-! ## Iterated quotients of a strong divisibility sequence -/

section Chain
variable (p : ℕ → ℕ)

/-- Iterated differences along the primes p 0, p 1, ... -/
def gd : ℕ → (ℕ → ℤ) → ℕ → ℤ
  | 0, f, n => f n
  | k + 1, f, n => gd k f (p k * n) - gd k f n

/-- Iterated quotients along the primes p 0, p 1, ... -/
def Gq (F : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => F n
  | k + 1, n => Gq F k (p k * n) / Gq F k n

lemma gd_shift (a : ℕ) : ∀ k f n, gd p k f (a * n) = gd p k (fun m => f (a * m)) n
  | 0, f, n => rfl
  | k + 1, f, n => by
    simp only [gd]
    rw [show p k * (a * n) = a * (p k * n) by ring, gd_shift a k f (p k * n), gd_shift a k f n]

lemma gd_add : ∀ k (f1 f2 : ℕ → ℤ) n,
    gd p k (fun m => f1 m + f2 m) n = gd p k f1 n + gd p k f2 n
  | 0, _, _, _ => rfl
  | k + 1, f1, f2, n => by
    simp only [gd]; rw [gd_add k, gd_add k]; ring

lemma gd_local : ∀ k (f1 f2 : ℕ → ℤ) n,
    (∀ d, d ∣ ∏ i ∈ range k, p i → f1 (n * d) = f2 (n * d)) → gd p k f1 n = gd p k f2 n
  | 0, f1, f2, n, h => by simpa [gd] using h 1 (by simp)
  | k + 1, f1, f2, n, h => by
    simp only [gd]
    rw [prod_range_succ] at h
    congr 1
    · refine gd_local k f1 f2 (p k * n) fun d hd => ?_
      have := h (p k * d) (by rw [mul_comm (∏ i ∈ range k, p i)]; exact mul_dvd_mul_left _ hd)
      rwa [show n * (p k * d) = p k * n * d by ring] at this
    · exact gd_local k f1 f2 n fun d hd => h d (hd.trans (dvd_mul_right _ _))

lemma gd_nonneg (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    ∀ k (f : ℕ → ℤ), (∀ m, 0 ≤ f m) →
      (∀ a b, 0 < a → 0 < b → f (Nat.gcd a b) = min (f a) (f b)) →
      ∀ n, 0 < n → 0 ≤ gd p k f n
  | 0, f, h0, _, n, _ => h0 n
  | k + 1, f, h0, hm, n, hn => by
    set f' : ℕ → ℤ := fun m => f (p k * m)
    set c : ℤ := f (n * ∏ i ∈ range k, p i)
    have hcop : Nat.Coprime (p k) (∏ i ∈ range k, p i) := by
      refine Nat.Coprime.prod_right fun i hi => ?_
      exact (Nat.coprime_primes (hp k) (hp i)).2 fun h => by
        have := hinj h; rw [mem_range] at hi; omega
    have hπ : 0 < ∏ i ∈ range k, p i := prod_pos fun i _ => (hp i).pos
    have h1 : gd p k f (p k * n) = gd p k f' n := gd_shift p (p k) k f n
    have h2 : gd p k f n = gd p k (fun m => min (f' m) c) n := by
      refine gd_local p k _ _ n fun d hd => ?_
      obtain ⟨e, he⟩ := hd
      have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at he; omega)
      have hg : Nat.gcd (p k * (n * d)) (n * ∏ i ∈ range k, p i) = n * d := by
        rw [he, show p k * (n * d) = n * d * p k by ring, show n * (d * e) = n * d * e by ring,
          Nat.gcd_mul_left]
        have : Nat.Coprime (p k) e := Nat.Coprime.coprime_dvd_right ⟨d, by rw [he]; ring⟩ hcop
        rw [this.gcd_eq_one, mul_one]
      have := hm (p k * (n * d)) (n * ∏ i ∈ range k, p i)
        (Nat.mul_pos (hp k).pos (Nat.mul_pos hn hd0)) (Nat.mul_pos hn hπ)
      rw [hg] at this
      exact this
    have h3 : gd p k f' n =
        gd p k (fun m => min (f' m) c) n + gd p k (fun m => max (f' m - c) 0) n := by
      rw [← gd_add]
      congr 1
      funext m
      omega
    have h4 : 0 ≤ gd p k (fun m => max (f' m - c) 0) n := by
      refine gd_nonneg hp hinj k _ (fun m => le_max_right _ _) ?_ n hn
      intro a b ha hb
      have := hm (p k * a) (p k * b) (Nat.mul_pos (hp k).pos ha) (Nat.mul_pos (hp k).pos hb)
      simp only [f']
      rw [← Nat.gcd_mul_left, this]
      omega
    show 0 ≤ gd p k f (p k * n) - gd p k f n
    rw [h1, h2]
    linarith

theorem Gq_spec (F : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hF : ∀ n, 0 < n → 0 < F n)
    (hsd : ∀ a b, 0 < a → 0 < b → F (Nat.gcd a b) = Nat.gcd (F a) (F b)) :
    ∀ k n, 0 < n → 0 < Gq p F k n ∧ Gq p F k n ∣ Gq p F k (p k * n) ∧
      ∀ l, ((Gq p F k n).factorization l : ℤ) = gd p k (fun m => ((F m).factorization l : ℤ)) n
  := by
  have hmeet : ∀ l, ∀ a b, 0 < a → 0 < b →
      (((F (Nat.gcd a b)).factorization l : ℕ) : ℤ) =
        min ((F a).factorization l : ℤ) ((F b).factorization l : ℤ) := by
    intro l a b ha hb
    rw [hsd a b ha hb, Nat.factorization_gcd (hF a ha).ne' (hF b hb).ne', Finsupp.inf_apply]
    push_cast
    rfl
  have hpos : ∀ k n, 0 < n → 0 < Gq p F k n ∧
      ∀ l, ((Gq p F k n).factorization l : ℤ) = gd p k (fun m => ((F m).factorization l : ℤ)) n := by
    intro k
    induction k with
    | zero => intro n hn; exact ⟨hF n hn, fun l => rfl⟩
    | succ k ih =>
      intro n hn
      obtain ⟨a1, a2⟩ := ih n hn
      obtain ⟨b1, b2⟩ := ih (p k * n) (Nat.mul_pos (hp k).pos hn)
      have hdvd : Gq p F k n ∣ Gq p F k (p k * n) := by
        rw [← Nat.factorization_le_iff_dvd a1.ne' b1.ne', Finsupp.le_def]
        intro l
        have := gd_nonneg p hp hinj (k + 1) (fun m => ((F m).factorization l : ℤ))
          (fun m => Nat.cast_nonneg _) (hmeet l) n hn
        simp only [gd] at this
        rw [← a2 l, ← b2 l] at this
        exact_mod_cast (sub_nonneg.1 this)
      refine ⟨Nat.div_pos (Nat.le_of_dvd b1 hdvd) a1, fun l => ?_⟩
      show (((Gq p F k (p k * n)) / Gq p F k n).factorization l : ℤ) = _
      rw [Nat.factorization_div hdvd, Finsupp.tsub_apply]
      have hle : (Gq p F k n).factorization l ≤ (Gq p F k (p k * n)).factorization l :=
        (Nat.factorization_le_iff_dvd a1.ne' b1.ne').2 hdvd l
      rw [Nat.cast_sub hle, a2 l, b2 l]
      rfl
  intro k n hn
  obtain ⟨a1, a2⟩ := hpos k n hn
  obtain ⟨b1, b2⟩ := hpos k (p k * n) (Nat.mul_pos (hp k).pos hn)
  refine ⟨a1, ?_, a2⟩
  rw [← Nat.factorization_le_iff_dvd a1.ne' b1.ne', Finsupp.le_def]
  intro l
  have := gd_nonneg p hp hinj (k + 1) (fun m => ((F m).factorization l : ℤ))
          (fun m => Nat.cast_nonneg _) (hmeet l) n hn
  simp only [gd] at this
  rw [← a2 l, ← b2 l] at this
  exact_mod_cast (sub_nonneg.1 this)

end Chain

/-! ## The conjecture -/

/-- G_1 = T, G_(k+1)(n) = G_k(p_k n) / G_k(n) with p_0 = 2, p_1 = 3, ... (README: G_(k+1)). -/
noncomputable def Gchain (j : ℕ) : ℕ → ℕ → ℕ := Gq (Nat.nth Nat.Prime) (T j)

theorem A192062_main (j k n : ℕ) (hn : 0 < n) :
    0 < Gchain j k n ∧ Gchain j k n ∣ Gchain j k (Nat.nth Nat.Prime k * n) ∧
      Gchain j k (Nat.nth Nat.Prime k * n) = Gchain j k n * Gchain j (k + 1) n := by
  obtain ⟨h1, h2, _⟩ := Gq_spec (Nat.nth Nat.Prime) (T j) Nat.prime_nth_prime
    (Nat.nth_injective Nat.infinite_setOfPred_prime) (T_pos j)
    (fun a b _ _ => (T_gcd j a b).symm) k n hn
  refine ⟨h1, h2, ?_⟩
  show _ = Gchain j k n * (Gchain j k (Nat.nth Nat.Prime k * n) / Gchain j k n)
  exact (Nat.mul_div_cancel' h2).symm

theorem A192062_G1 (j n : ℕ) (hn : 0 < n) : Gchain j 1 n = A j n := by
  show T j (Nat.nth Nat.Prime 0 * n) / T j n = A j n
  rw [Nat.nth_prime_zero_eq_two, T_double]
  exact Nat.mul_div_cancel _ (T_pos j n hn)
