/-
OEIS A195507: a(n) = least m > n with m ≡ n (mod k) for k = 1..n-1.
Conjecture: with a(n)/n = num/d in lowest terms, a(n+1) = d a(n) - (d-1) n + 1.
True. a(n) = n + L(n) with L(n) = lcm(1..n-1) (m - n must be a positive common
multiple of 1..n-1; Adams-Watters 2011). The reduced denominator of a(n)/n is
d = n / gcd(n + L, n) = n / gcd(L, n), and
L(n+1) = lcm(L, n) = L n / gcd(L, n) = d L, so
a(n+1) = n + 1 + d L = d (n + L) - (d - 1) n + 1.

Checked here (core Lean): `recurrence`, for all n ≥ 1 and every L:
with d = n / gcd(n + L, n), (n + 1) + lcm L n = d (n + L) - (d - 1) n + 1.
Also `small`: a(n) = n + lcm(1..n-1) by brute force for n ≤ 9.
Not checked here: the general step "m ≡ n mod k for all k < n iff L | m - n"
(lcm is the least common multiple), used only to identify a(n) = n + L(n).
-/

theorem gcd_add (n L : Nat) : Nat.gcd (n + L) n = Nat.gcd L n := by
  rw [Nat.gcd_comm, Nat.gcd_comm L n, Nat.add_comm, Nat.gcd_add_self_right]

theorem recurrence (n L : Nat) (hn : 1 ≤ n) :
    (n + 1) + Nat.lcm L n = (n / Nat.gcd (n + L) n) * (n + L) - (n / Nat.gcd (n + L) n - 1) * n + 1 := by
  rw [gcd_add]
  have hg : Nat.gcd L n ∣ n := Nat.gcd_dvd_right L n
  have hgpos : 0 < Nat.gcd L n := Nat.gcd_pos_of_pos_right L (by omega)
  obtain ⟨d, hd⟩ := hg
  have hdn : n / Nat.gcd L n = d :=
    Nat.div_eq_of_eq_mul_left hgpos (by rw [Nat.mul_comm]; exact hd)
  have hlcm : Nat.lcm L n = L * d := by
    unfold Nat.lcm
    apply Nat.div_eq_of_eq_mul_left hgpos
    calc L * n = L * (Nat.gcd L n * d) := by rw [← hd]
      _ = L * d * Nat.gcd L n := by rw [Nat.mul_comm (Nat.gcd L n) d, Nat.mul_assoc]
  rw [hdn, hlcm]
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, Nat.mul_zero] at hd; omega
    · exact h0
  have e1 : d * (n + L) = d * n + L * d := by rw [Nat.mul_add, Nat.mul_comm d L]
  have e2 : (d - 1) * n + n = d * n := by
    rw [Nat.sub_mul, Nat.one_mul]; have : n ≤ d * n := Nat.le_mul_of_pos_left n hd1; omega
  omega

def lcmUpTo (n : Nat) : Nat := (List.range (n - 1)).foldl (fun acc k => Nat.lcm acc (k + 1)) 1

/-- least m > n, m ≤ n + bound, with m ≡ n mod k for all k < n -/
def brute (n bound : Nat) : Nat :=
  ((List.range bound).map (fun i => n + 1 + i)).find? (fun m => (List.range (n - 1)).all (fun k => m % (k + 1) == n % (k + 1))) |>.getD 0

theorem small : (List.range 9).all (fun i => brute (i + 1) 1000 == (i + 1) + lcmUpTo (i + 1)) = true := by decide +kernel
