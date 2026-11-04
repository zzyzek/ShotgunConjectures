/-
OEIS A126142 (primes p whose square has prime digit sum). Comment (Librandi
2009): "a(n)^2 is of the form 6*k+1". Trivially true, and more: every
integer n with gcd(n, 6) = 1 has n^2 ≡ 1 (mod 24); every prime p > 3 is such
an n, and all terms of A126142 are primes ≥ 5 (the first is 5).

Checked here: `sq_mod_24` for every n (core Lean, a finite check over
residues mod 24 plus `Nat.pow_mod`).
Not checked here: that the terms are primes > 3 (the definition of A126142
and a(1) = 5).
-/

theorem residues : ∀ r, r < 24 → r % 2 = 1 → r % 3 ≠ 0 → r ^ 2 % 24 = 1 := by decide

theorem sq_mod_24 (n : Nat) (h2 : n % 2 = 1) (h3 : n % 3 ≠ 0) : n ^ 2 % 24 = 1 := by
  have hr : n % 24 < 24 := Nat.mod_lt _ (by decide)
  have e : n ^ 2 % 24 = (n % 24) ^ 2 % 24 := Nat.pow_mod n 2 24
  rw [e]
  exact residues (n % 24) hr (by omega) (by omega)

theorem sq_form_6k1 (n : Nat) (h2 : n % 2 = 1) (h3 : n % 3 ≠ 0) : n ^ 2 % 6 = 1 := by
  have := sq_mod_24 n h2 h3
  omega
