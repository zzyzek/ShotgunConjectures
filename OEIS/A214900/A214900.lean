/-
OEIS A214900: number of ordered representations n = x^2 + y^2 + z^2 + w^4.
Conjecture: a(n) ≠ 0 for all n. True, given Legendre's three-square theorem
(m is a sum of three squares unless m = 4^a (8b + 7)).

Reduction. If n is not of the form 4^a (8b+7), take w = 0. Otherwise:
a = 0: n - 1 = 8b + 6 is ≡ 2 (mod 4), not excluded, so w = 1 works;
a = 1: n - 1 = 32b + 27 is odd and ≡ 3 (mod 8), not excluded, so w = 1 works;
a ≥ 2: n = 16 m with m smaller; from m = x^2 + y^2 + z^2 + w^4 get
n = (4x)^2 + (4y)^2 + (4z)^2 + (2w)^4.

Checked here (core Lean): `main`, all n, with Legendre's theorem (only the
direction "not excluded ⇒ sum of three squares") as a hypothesis.
Not checked here: Legendre's three-square theorem itself.
-/

def excluded (m : Nat) : Prop := ∃ a b, m = 4 ^ a * (8 * b + 7)

theorem mod4_of_pos_pow (c k : Nat) : (4 ^ (c + 1) * k) % 4 = 0 := by
  rw [Nat.pow_succ, Nat.mul_right_comm, Nat.mul_comm _ 4]
  exact Nat.mul_mod_right 4 _

theorem not_excl_8b6 (b : Nat) : ¬ excluded (8 * b + 6) := by
  rintro ⟨c, d, h⟩
  cases c with
  | zero => simp at h; omega
  | succ c => have := mod4_of_pos_pow c (8 * d + 7); omega

theorem not_excl_32b27 (b : Nat) : ¬ excluded (32 * b + 27) := by
  rintro ⟨c, d, h⟩
  cases c with
  | zero => simp at h; omega
  | succ c => have := mod4_of_pos_pow c (8 * d + 7); omega

theorem main (legendre : ∀ m : Nat, ¬ excluded m → ∃ x y z : Nat, m = x ^ 2 + y ^ 2 + z ^ 2) :
    ∀ n : Nat, ∃ x y z w : Nat, n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 4 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hex : excluded n
    · obtain ⟨a, b, hab⟩ := hex
      match a, hab with
      | 0, hab =>
        obtain ⟨x, y, z, h⟩ := legendre (8 * b + 6) (not_excl_8b6 b)
        exact ⟨x, y, z, 1, by simp at hab; omega⟩
      | 1, hab =>
        obtain ⟨x, y, z, h⟩ := legendre (32 * b + 27) (not_excl_32b27 b)
        exact ⟨x, y, z, 1, by simp at hab; omega⟩
      | a + 2, hab =>
        have e : n = 16 * (4 ^ a * (8 * b + 7)) := by
          rw [hab, Nat.pow_add, Nat.mul_comm (4 ^ a) (4 ^ 2), Nat.mul_assoc]
        have hpos : 0 < 4 ^ a * (8 * b + 7) := Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
        obtain ⟨x, y, z, w, h⟩ := ih (4 ^ a * (8 * b + 7)) (by omega)
        refine ⟨4 * x, 4 * y, 4 * z, 2 * w, ?_⟩
        rw [e, h]
        simp only [Nat.mul_pow]
        omega
    · obtain ⟨x, y, z, h⟩ := legendre n hex
      exact ⟨x, y, z, 0, by simp [h]⟩
