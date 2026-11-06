/-
OEIS A005329, Mathlib proof.

A005329: c(n) = Product_{i=1..n} (2^i - 1) (`A005329_c`, over ℚ).
A075271: a(0) = 1 and (BM a)(n) = 2 a(n-1) for n ≥ 1, where the
BinomialMean transform is (BM a)(n) = (Sum_{k=0..n} C(n,k) a(k)) / 2^n
(`A005329_BM`). A075272 = BM A075271.

Layman's conjecture in A005329: A005329 is the inverse binomial transform
of A075272 = BM(A075271).

Main theorem `A005329_main`: for every a : ℕ → ℚ with a 0 = 1 and
BM a (n+1) = 2 a n for all n,
  (1) BM a n = Sum_{k=0..n} C(n,k) c(k) for all n (A075272 is the
      binomial transform of A005329), and
  (2) c n = Sum_{k=0..n} (-1)^(n-k) C(n,k) (BM a k) for all n
      (A005329 is the inverse binomial transform of A075272).
`A005329_exists`: such an a exists (a(n) = b(n+1)/2 with b the binomial
transform of c), so the hypotheses describe A075271 exactly
(`A005329_unique`: they determine a).

Proof: with b = binomial transform of c, Pascal's rule gives
b(k+1) = Sum_j C(k,j) (c j + c (j+1)) = Sum_j C(k,j) 2^(j+1) c(j), since
c(j+1) = (2^(j+1) - 1) c(j). The two-fold binomial transform with weight x
(`A005329_twofold`) gives Sum_k C(n,k) b(k+1) = 2^(n+1) b(n), i.e.
n ↦ b(n+1)/2 satisfies the A075271 recurrence; the recurrence has a unique
solution. Case x = -1 of `A005329_twofold` is binomial inversion.

Not checked: that the definitions match the OEIS text (they are transcribed
from the A005329, A075271 and A075272 entries); the integer values are not
used.
-/
import Mathlib

open Finset

/-- A005329 over ℚ: c(n) = Product_{i=1..n} (2^i - 1). -/
def A005329_c (n : ℕ) : ℚ := ∏ i ∈ range n, ((2 : ℚ) ^ (i + 1) - 1)

/-- Binomial transform: (T f)(n) = Sum_{k=0..n} C(n,k) f(k). -/
def A005329_T (f : ℕ → ℚ) (n : ℕ) : ℚ := ∑ k ∈ range (n + 1), (n.choose k : ℚ) * f k

/-- BinomialMean transform: (BM f)(n) = (T f)(n) / 2^n. -/
def A005329_BM (f : ℕ → ℚ) (n : ℕ) : ℚ := A005329_T f n / 2 ^ n

/-- Pascal's rule inside a binomial transform. -/
theorem A005329_pascal (f : ℕ → ℚ) (k : ℕ) :
    ∑ j ∈ range (k + 2), ((k + 1).choose j : ℚ) * f j =
      ∑ j ∈ range (k + 1), (k.choose j : ℚ) * (f j + f (j + 1)) := by
  rw [sum_range_succ']
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib]
  have h : ∑ j ∈ range (k + 2), (k.choose j : ℚ) * f j =
      ∑ j ∈ range (k + 1), (k.choose (j + 1) : ℚ) * f (j + 1) + (k.choose 0 : ℚ) * f 0 := by
    rw [sum_range_succ']
  rw [sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero] at h
  simp only [mul_add, sum_add_distrib, Nat.choose_zero_right] at h ⊢
  linarith

/-- Two-fold binomial transform with weight x:
Sum_k C(n,k) x^(n-k) (T d)(k) = Sum_j C(n,j) (x+1)^(n-j) d(j). -/
theorem A005329_twofold (x : ℚ) (n : ℕ) : ∀ d : ℕ → ℚ,
    ∑ k ∈ range (n + 1), (n.choose k : ℚ) * (x ^ (n - k) * A005329_T d k) =
      ∑ j ∈ range (n + 1), (n.choose j : ℚ) * ((x + 1) ^ (n - j) * d j) := by
  induction n with
  | zero => intro d; simp [A005329_T]
  | succ n ih =>
    intro d
    rw [A005329_pascal, A005329_pascal]
    have hl : ∀ k ∈ range (n + 1),
        (n.choose k : ℚ) * (x ^ (n + 1 - k) * A005329_T d k + x ^ (n + 1 - (k + 1)) * A005329_T d (k + 1)) =
          (n.choose k : ℚ) * (x ^ (n - k) * A005329_T (fun j => (x + 1) * d j + d (j + 1)) k) := by
      intro k hk
      have hk' : n + 1 - k = n - k + 1 := by rw [mem_range] at hk; omega
      have hk'' : n + 1 - (k + 1) = n - k := by omega
      have hT : A005329_T d (k + 1) = ∑ j ∈ range (k + 1), (k.choose j : ℚ) * (d j + d (j + 1)) := by
        unfold A005329_T; exact A005329_pascal d k
      rw [hk', hk'', hT]
      unfold A005329_T
      rw [pow_succ]
      have : x * ∑ j ∈ range (k + 1), (k.choose j : ℚ) * d j +
          ∑ j ∈ range (k + 1), (k.choose j : ℚ) * (d j + d (j + 1)) =
          ∑ j ∈ range (k + 1), (k.choose j : ℚ) * ((x + 1) * d j + d (j + 1)) := by
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl (fun j _ => by ring)
      rw [← this]; ring
    have hr : ∀ j ∈ range (n + 1),
        (n.choose j : ℚ) * ((x + 1) ^ (n + 1 - j) * d j + (x + 1) ^ (n + 1 - (j + 1)) * d (j + 1)) =
          (n.choose j : ℚ) * ((x + 1) ^ (n - j) * ((x + 1) * d j + d (j + 1))) := by
      intro j hj
      have hj' : n + 1 - j = n - j + 1 := by rw [mem_range] at hj; omega
      have hj'' : n + 1 - (j + 1) = n - j := by omega
      rw [hj', hj'', pow_succ]; ring
    rw [sum_congr rfl hl, sum_congr rfl hr]
    exact ih _

/-- c(j+1) = (2^(j+1) - 1) c(j). -/
theorem A005329_c_succ (j : ℕ) : A005329_c (j + 1) = A005329_c j * ((2 : ℚ) ^ (j + 1) - 1) := by
  unfold A005329_c; rw [prod_range_succ]

/-- b(k+1) = Sum_j C(k,j) 2^(j+1) c(j), with b = T c. -/
theorem A005329_b_succ (k : ℕ) :
    A005329_T A005329_c (k + 1) = A005329_T (fun j => 2 ^ (j + 1) * A005329_c j) k := by
  unfold A005329_T
  rw [A005329_pascal]
  exact sum_congr rfl (fun j _ => by rw [A005329_c_succ]; ring)

/-- Sum_k C(n,k) b(k+1) = 2^(n+1) b(n). -/
theorem A005329_key (n : ℕ) :
    A005329_T (fun k => A005329_T A005329_c (k + 1)) n = 2 ^ (n + 1) * A005329_T A005329_c n := by
  set g : ℕ → ℚ := fun j => 2 ^ (j + 1) * A005329_c j with hg
  have h1 := A005329_twofold 1 n g
  have hf : (fun k => A005329_T A005329_c (k + 1)) = fun k => A005329_T g k :=
    funext A005329_b_succ
  rw [hf]
  show ∑ k ∈ range (n + 1), (n.choose k : ℚ) * A005329_T g k = _
  rw [show ∑ k ∈ range (n + 1), (n.choose k : ℚ) * A005329_T g k =
      ∑ k ∈ range (n + 1), (n.choose k : ℚ) * ((1 : ℚ) ^ (n - k) * A005329_T g k) from
      sum_congr rfl (fun k _ => by rw [one_pow, one_mul]), h1]
  unfold A005329_T
  rw [mul_sum]
  refine sum_congr rfl (fun j hj => ?_)
  have hj' : n + 1 = (n - j) + (j + 1) := by rw [mem_range] at hj; omega
  rw [show (1 : ℚ) + 1 = 2 by norm_num, hj', pow_add, hg]; ring

/-- The A075271 recurrence determines the sequence. -/
theorem A005329_unique (a a' : ℕ → ℚ) (h0 : a 0 = 1) (h0' : a' 0 = 1)
    (h : ∀ n, A005329_BM a (n + 1) = 2 * a n) (h' : ∀ n, A005329_BM a' (n + 1) = 2 * a' n) :
    ∀ n, a n = a' n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [h0, h0']
    | succ m =>
      have e := h m
      have e' := h' m
      unfold A005329_BM A005329_T at e e'
      rw [div_eq_iff (by positivity), sum_range_succ, Nat.choose_self] at e e'
      have hs : ∑ k ∈ range (m + 1), ((m + 1).choose k : ℚ) * a k =
          ∑ k ∈ range (m + 1), ((m + 1).choose k : ℚ) * a' k :=
        sum_congr rfl (fun k hk => by rw [ih k (by rw [mem_range] at hk; omega)])
      have hm : a m = a' m := ih m (by omega)
      rw [hs, hm] at e
      simp only [Nat.cast_one, one_mul] at e e'
      linarith

/-- A075271 exists: a(n) = b(n+1)/2 satisfies a(0) = 1 and BM a (n+1) = 2 a(n). -/
theorem A005329_exists :
    (fun n => A005329_T A005329_c (n + 1) / 2) 0 = 1 ∧
      ∀ n, A005329_BM (fun n => A005329_T A005329_c (n + 1) / 2) (n + 1) =
        2 * A005329_T A005329_c (n + 1) / 2 := by
  constructor
  · simp [A005329_T, A005329_c, sum_range_succ]
  · intro n
    have hk := A005329_key (n + 1)
    unfold A005329_BM
    have : A005329_T (fun n => A005329_T A005329_c (n + 1) / 2) (n + 1) =
        A005329_T (fun k => A005329_T A005329_c (k + 1)) (n + 1) / 2 := by
      unfold A005329_T; rw [sum_div]; exact sum_congr rfl (fun k _ => by ring)
    rw [this, hk]
    field_simp
    ring

/-- Binomial inversion: Sum_k (-1)^(n-k) C(n,k) (T d)(k) = d(n). -/
theorem A005329_inversion (d : ℕ → ℚ) (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * A005329_T d k = d n := by
  have h := A005329_twofold (-1) n d
  rw [show (-1 : ℚ) + 1 = 0 by norm_num,
    sum_range_succ (fun j => (n.choose j : ℚ) * ((0 : ℚ) ^ (n - j) * d j))] at h
  have hz : ∑ j ∈ range n, (n.choose j : ℚ) * ((0 : ℚ) ^ (n - j) * d j) = 0 :=
    sum_eq_zero (fun j hj => by
      rw [mem_range] at hj
      rw [zero_pow (by omega)]; ring)
  rw [hz, Nat.choose_self, Nat.sub_self] at h
  simp only [pow_zero, Nat.cast_one, one_mul, zero_add] at h
  rw [← h]
  exact sum_congr rfl (fun k _ => by ring)

/-- Layman's conjecture (A005329): for A075271 (a 0 = 1, BM a (n+1) = 2 a n),
A075272 = BM a is the binomial transform of A005329, and A005329 is the
inverse binomial transform of A075272. -/
theorem A005329_main (a : ℕ → ℚ) (h0 : a 0 = 1) (h : ∀ n, A005329_BM a (n + 1) = 2 * a n) :
    (∀ n, A005329_BM a n = A005329_T A005329_c n) ∧
      (∀ n, A005329_c n =
        ∑ k ∈ range (n + 1), (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * A005329_BM a k) := by
  have hex := A005329_exists
  have hu := A005329_unique a _ h0 hex.1 h (fun n => by rw [hex.2 n]; ring)
  have hbm : ∀ n, A005329_BM a n = A005329_T A005329_c n := by
    intro n
    cases n with
    | zero => simp [A005329_BM, A005329_T, A005329_c, h0]
    | succ m => rw [h m, hu m]; ring
  refine ⟨hbm, fun n => ?_⟩
  simp only [hbm]
  exact (A005329_inversion A005329_c n).symm
