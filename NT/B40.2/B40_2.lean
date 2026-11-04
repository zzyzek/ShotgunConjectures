/-
NT-B40.2 (Guy, UPINT 3rd ed., B40, Recamán): "does the set of totatives of
every sufficiently large n contain a Pythagorean triple?"  No.

Checked here (core Lean, no Mathlib):
* `no_triple`: if 2 ∣ n, 3 ∣ n or 5 ∣ n, and a, b, c are each coprime to n,
  then a^2 + b^2 ≠ c^2.  Every totative of n is coprime to n, so no n
  divisible by 2, 3 or 5 (infinitely many n) has a Pythagorean triple among
  its totatives.
Not checked here: nothing else is claimed.
-/

theorem not_dvd_of_coprime (p n x : Nat) (hp : 1 < p) (hpn : p ∣ n) (h : Nat.gcd x n = 1) :
    x % p ≠ 0 := by
  intro hx
  have hd : p ∣ Nat.gcd x n := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hx) hpn
  rw [h] at hd
  have := Nat.le_of_dvd (by decide) hd
  omega

theorem sq_mod (m x : Nat) : x ^ 2 % m = (x % m) ^ 2 % m := Nat.pow_mod x 2 m

theorem sum_sq_mod (m a b : Nat) : (a ^ 2 + b ^ 2) % m = ((a % m) ^ 2 % m + (b % m) ^ 2 % m) % m := by
  rw [Nat.add_mod, sq_mod m a, sq_mod m b]

theorem key2 : ∀ x y z : Fin 4, x.val % 2 ≠ 0 → y.val % 2 ≠ 0 →
    (x.val ^ 2 % 4 + y.val ^ 2 % 4) % 4 ≠ z.val ^ 2 % 4 := by decide
theorem key3 : ∀ x y z : Fin 3, x.val ≠ 0 → y.val ≠ 0 →
    (x.val ^ 2 % 3 + y.val ^ 2 % 3) % 3 ≠ z.val ^ 2 % 3 := by decide
theorem key5 : ∀ x y z : Fin 5, x.val ≠ 0 → y.val ≠ 0 → z.val ≠ 0 →
    (x.val ^ 2 % 5 + y.val ^ 2 % 5) % 5 ≠ z.val ^ 2 % 5 := by decide

theorem no_triple (n a b c : Nat) (hn : 2 ∣ n ∨ 3 ∣ n ∨ 5 ∣ n)
    (ha : Nat.gcd a n = 1) (hb : Nat.gcd b n = 1) (hc : Nat.gcd c n = 1) :
    a ^ 2 + b ^ 2 ≠ c ^ 2 := by
  intro h
  rcases hn with h2 | h3 | h5
  · have ha2 := not_dvd_of_coprime 2 n a (by decide) h2 ha
    have hb2 := not_dvd_of_coprime 2 n b (by decide) h2 hb
    have e : (a ^ 2 + b ^ 2) % 4 = c ^ 2 % 4 := by rw [h]
    rw [sum_sq_mod, sq_mod 4 c] at e
    exact key2 ⟨a % 4, Nat.mod_lt _ (by decide)⟩ ⟨b % 4, Nat.mod_lt _ (by decide)⟩
      ⟨c % 4, Nat.mod_lt _ (by decide)⟩
      (show a % 4 % 2 ≠ 0 by omega) (show b % 4 % 2 ≠ 0 by omega) e
  · have ha3 := not_dvd_of_coprime 3 n a (by decide) h3 ha
    have hb3 := not_dvd_of_coprime 3 n b (by decide) h3 hb
    have e : (a ^ 2 + b ^ 2) % 3 = c ^ 2 % 3 := by rw [h]
    rw [sum_sq_mod, sq_mod 3 c] at e
    exact key3 ⟨a % 3, Nat.mod_lt _ (by decide)⟩ ⟨b % 3, Nat.mod_lt _ (by decide)⟩
      ⟨c % 3, Nat.mod_lt _ (by decide)⟩ ha3 hb3 e
  · have ha5 := not_dvd_of_coprime 5 n a (by decide) h5 ha
    have hb5 := not_dvd_of_coprime 5 n b (by decide) h5 hb
    have hc5 := not_dvd_of_coprime 5 n c (by decide) h5 hc
    have e : (a ^ 2 + b ^ 2) % 5 = c ^ 2 % 5 := by rw [h]
    rw [sum_sq_mod, sq_mod 5 c] at e
    exact key5 ⟨a % 5, Nat.mod_lt _ (by decide)⟩ ⟨b % 5, Nat.mod_lt _ (by decide)⟩
      ⟨c % 5, Nat.mod_lt _ (by decide)⟩ ha5 hb5 hc5 e
