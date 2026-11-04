/-
OEIS A195507, Mathlib proof.

A195507(n) = smallest m > n with m ≡ n (mod k) for k = 1, ..., n-1 (n ≥ 1).
Conjecture: write a(n)/n in lowest terms as num/d; then
a(n+1) = d·a(n) - (d-1)·n + 1.

Main theorem `A195507_main`: with `A195507 n` defined as `Nat.find` of
"∃ m, n < m ∧ ∀ k ∈ [1, n-1], m ≡ n [MOD k]" and d = the denominator of
the rational a(n)/n in lowest terms (`Rat.den`), for every n ≥ 1
  (a(n+1) : ℤ) = d·a(n) - (d-1)·n + 1.
This is the README result. Along the way `A195507_eq`: a(n) = n + lcm(1..n-1)
(Adams-Watters). Nothing is outside Lean.
-/
import Mathlib

/-- lcm(1, ..., n-1) (= 1 for n ≤ 1). -/
def A195507_L (n : ℕ) : ℕ := (Finset.Icc 1 (n - 1)).lcm id

theorem A195507_L_pos (n : ℕ) : 0 < A195507_L n := by
  apply Nat.pos_of_ne_zero
  rw [A195507_L, Ne, Finset.lcm_eq_zero_iff]
  simp

theorem A195507_cond_iff (n m : ℕ) (h : n ≤ m) :
    (∀ k ∈ Finset.Icc 1 (n - 1), m ≡ n [MOD k]) ↔ A195507_L n ∣ m - n := by
  rw [A195507_L, Finset.lcm_dvd_iff]
  refine forall₂_congr fun k _ => ?_
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' h, id]

theorem A195507_exists (n : ℕ) :
    ∃ m, n < m ∧ ∀ k ∈ Finset.Icc 1 (n - 1), m ≡ n [MOD k] :=
  ⟨n + A195507_L n, by have := A195507_L_pos n; omega,
    (A195507_cond_iff n _ (by omega)).2 (by simp)⟩

/-- A195507(n): smallest m > n with m ≡ n (mod k) for 1 ≤ k ≤ n - 1. -/
noncomputable def A195507 (n : ℕ) : ℕ := Nat.find (A195507_exists n)

theorem A195507_eq (n : ℕ) : A195507 n = n + A195507_L n := by
  have hL := A195507_L_pos n
  rw [A195507, Nat.find_eq_iff]
  refine ⟨⟨by omega, (A195507_cond_iff n _ (by omega)).2 (by simp)⟩, ?_⟩
  rintro m hm ⟨hnm, hc⟩
  have hd := (A195507_cond_iff n m hnm.le).1 hc
  have := Nat.le_of_dvd (by omega) hd
  omega

theorem A195507_L_succ (n : ℕ) (hn : 1 ≤ n) :
    A195507_L (n + 1) = Nat.lcm (A195507_L n) n := by
  have hs : Finset.Icc 1 (n + 1 - 1) = insert n (Finset.Icc 1 (n - 1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [A195507_L, hs, Finset.lcm_insert, id, ← A195507_L, Nat.lcm_comm]
  rfl

theorem A195507_main (n : ℕ) (hn : 1 ≤ n) :
    let d := ((A195507 n : ℚ) / n).den
    (A195507 (n + 1) : ℤ) = d * A195507 n - (d - 1) * n + 1 := by
  intro d
  set L := A195507_L n with hL
  set g := Nat.gcd L n with hg
  have hLpos := A195507_L_pos n
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hLpos
  have hgn : g ∣ n := Nat.gcd_dvd_right L n
  have hgL : g ∣ L := Nat.gcd_dvd_left L n
  have hgnL : Nat.gcd (n + L) n = g := by
    rw [hg, Nat.gcd_comm L n, Nat.gcd_comm (n + L) n, Nat.add_comm n L, Nat.gcd_add_self_right]
  /- d = n / g -/
  have hd : d = n / g := by
    have h1 : g ∣ n + L := Nat.dvd_add hgn hgL
    have hcop : Nat.Coprime ((n + L) / g) (n / g) := by
      have := Nat.coprime_div_gcd_div_gcd (m := n + L) (n := n) (by rw [hgnL]; exact hgpos)
      rwa [hgnL] at this
    have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hgpos.ne'
    have e1 : (((n + L) / g : ℕ) : ℚ) = ((n + L : ℕ) : ℚ) / g := Nat.cast_div h1 hgq
    have e2 : ((n / g : ℕ) : ℚ) = (n : ℚ) / g := Nat.cast_div hgn hgq
    have hq : ((A195507 n : ℚ) / n) = (((n + L) / g : ℕ) : ℤ) / (((n / g : ℕ) : ℤ) : ℚ) := by
      rw [Int.cast_natCast, Int.cast_natCast, e1, e2, A195507_eq]
      have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      field_simp
      rfl
    have hpos : (0 : ℤ) < ((n / g : ℕ) : ℤ) := by
      exact_mod_cast Nat.div_pos (Nat.le_of_dvd (by omega) hgn) hgpos
    have := Rat.den_div_eq_of_coprime (a := (((n + L) / g : ℕ) : ℤ)) hpos
      (by rw [Int.natAbs_natCast, Int.natAbs_natCast]; exact hcop)
    simp only [d, hq]
    exact_mod_cast this
  /- d·L = lcm(L, n) = L(n+1) -/
  have hdL : d * L = A195507_L (n + 1) := by
    rw [A195507_L_succ n hn, Nat.lcm, hd, ← hg, Nat.div_mul_right_comm hgn, Nat.mul_comm n L]
  rw [A195507_eq (n + 1), A195507_eq n, ← hdL]
  have hd1 : 1 ≤ d := Rat.den_pos _
  push_cast [hd1]
  ring
