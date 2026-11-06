import Mathlib

/-
OEIS A078173: a(n) = max(min(r,s,t)) over positive integer solutions of
r*s*t = n*(r+s+t).  Conjecture (comment in the entry): over all positive
integer solutions r <= s <= t, max(t) = n*(n+2) and max(s) = 2*n.

`Sol n r s t` is: 0 < r, r ≤ s ≤ t, r*s*t = n*(r+s+t) (in ℕ).
Main theorems (for every n ≥ 1):
* `A078173_max_t`: IsGreatest {t | ∃ r s, Sol n r s t} (n*(n+2)),
* `A078173_max_s`: IsGreatest {s | ∃ r t, Sol n r s t} (2*n).
Witnesses (1, n+1, n(n+2)) and (1, 2n, 2n+1).  Fully checked; nothing outside Lean
except the reading of the comment.
-/

def A078173.Sol (n r s t : ℕ) : Prop := 0 < r ∧ r ≤ s ∧ s ≤ t ∧ r * s * t = n * (r + s + t)

theorem A078173.t_le {n r s t : ℕ} (h : A078173.Sol n r s t) : t ≤ n * (n + 2) := by
  obtain ⟨hr, hrs, hst, he⟩ := h
  have hz : ((r : ℤ) * s * t) = n * (r + s + t) := by exact_mod_cast he
  have hrZ : (0 : ℤ) < r := by exact_mod_cast hr
  have hsZ : (r : ℤ) ≤ s := by exact_mod_cast hrs
  have htZ : (s : ℤ) ≤ t := by exact_mod_cast hst
  have hn : (0 : ℤ) ≤ n := by positivity
  -- rs > n, since t(rs - n) = n(r+s) > 0
  have hd : (n : ℤ) + 1 ≤ r * s := by
    by_contra hc
    push Not at hc
    have : (r : ℤ) * s ≤ n := by omega
    nlinarith [mul_le_mul_of_nonneg_right this (by linarith : (0:ℤ) ≤ t)]
  suffices (t : ℤ) ≤ n * (n + 2) by exact_mod_cast this
  rcases (show r = 1 ∨ 2 ≤ r by omega) with h1 | h2
  · subst h1
    simp only [Nat.cast_one, one_mul] at hz hd
    -- (s - n)(t - n) = n(n+1), s - n ≥ 1
    have key : ((s : ℤ) - n) * (t - n) = n * (n + 1) := by nlinarith
    nlinarith
  · have h2Z : (2 : ℤ) ≤ r := by exact_mod_cast h2
    by_contra hc
    push Not at hc
    have e2 : (t : ℤ) * (r * s - n) = n * (r + s) := by nlinarith
    have hrs2 : 2 * ((r : ℤ) + s) ≤ r * s + 4 := by nlinarith
    obtain ⟨d, hdd, hdef⟩ : ∃ d : ℤ, 1 ≤ d ∧ (r : ℤ) * s = n + d := ⟨r * s - n, by linarith, by ring⟩
    rw [hdef] at e2 hrs2
    have A : 2 * ((t : ℤ) * d) ≤ n * (n + d + 4) := by
      have := mul_le_mul_of_nonneg_left hrs2 hn
      have e3 : (t : ℤ) * d = n * (r + s) := by rw [← e2]; ring
      nlinarith
    have B : ((n : ℤ) * (n + 2) + 1) * d ≤ t * d :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have C : (0 : ℤ) ≤ (d - 1) * (2 * n ^ 2 + 3 * n + 2) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [sq_nonneg ((n : ℤ) - 1)]

theorem A078173.s_le {n r s t : ℕ} (h : A078173.Sol n r s t) : s ≤ 2 * n := by
  obtain ⟨hr, hrs, hst, he⟩ := h
  have hz : ((r : ℤ) * s * t) = n * (r + s + t) := by exact_mod_cast he
  have hrZ : (1 : ℤ) ≤ r := by exact_mod_cast hr
  have hsZ : (r : ℤ) ≤ s := by exact_mod_cast hrs
  have htZ : (s : ℤ) ≤ t := by exact_mod_cast hst
  have hn : (0 : ℤ) ≤ n := by positivity
  by_contra hc
  push Not at hc
  have hcZ : 2 * (n : ℤ) + 1 ≤ s := by exact_mod_cast hc
  -- s(rs - 2n) ≤ n r from t ≥ s, while rs - 2n ≥ r
  have e2 : (t : ℤ) * (r * s - n) = n * (r + s) := by nlinarith
  have hd : (r : ℤ) ≤ r * s - 2 * n := by nlinarith
  have h3 : (s : ℤ) * (r * s - n) ≤ n * (r + s) := by
    nlinarith [mul_le_mul_of_nonneg_right htZ (by nlinarith : (0:ℤ) ≤ r * s - n)]
  nlinarith

theorem A078173_max_t (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest {t | ∃ r s, A078173.Sol n r s t} (n * (n + 2)) := by
  refine ⟨⟨1, n + 1, ?_, ?_, ?_, ?_⟩, ?_⟩
  · omega
  · omega
  · nlinarith
  · ring
  · rintro t ⟨r, s, h⟩
    exact A078173.t_le h

theorem A078173_max_s (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest {s | ∃ r t, A078173.Sol n r s t} (2 * n) := by
  refine ⟨⟨1, 2 * n + 1, ?_, ?_, ?_, ?_⟩, ?_⟩
  · omega
  · omega
  · omega
  · ring
  · rintro s ⟨r, t, h⟩
    exact A078173.s_le h
