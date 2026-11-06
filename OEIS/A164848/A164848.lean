/-
OEIS A164848: a(n) = A026741(n)/A051712(n+1), n ≥ 1. Conjecture (Curtz 2009):
a(n+24) = a(n).

Checked here (core Lean, no Mathlib), from the definitions:
* A026741(n) = n for odd n, n/2 for even n.
* A051712(n) = numerator of b(n) - b(n+1), b(n) = n/((n+1)(n+2)), computed in `Rat`.
* `A051712_succ`: A051712(n+1) = n / gcd(n, 24) for n ≥ 1.
* `A164848_closed`: a(n) = gcd(n, 24) for odd n and gcd(n, 24)/2 for even n.
* `A164848_periodic`: a(n + 24) = a(n) for all n ≥ 1 (the conjecture).
* `A164848_terms`: a(1..48) equal the listed terms.
Not checked here: that these definitions are the OEIS ones (compared with the listed
terms in certificate/check.gp).
-/

/-- b(n) = n/((n+1)(n+2)) as a rational (`Rat.divInt a b` is a/b, core `Rat.divInt_eq_div`). -/
def b (n : Nat) : Rat := Rat.divInt (n : Int) (((n + 1) * (n + 2) : Nat) : Int)

/-- A051712(n) = numerator of b(n) - b(n+1) (nonnegative for n ≥ 1). -/
def A051712 (n : Nat) : Nat := (b n - b (n + 1)).num.natAbs

def A026741 (n : Nat) : Nat := if n % 2 = 1 then n else n / 2

def A164848 (n : Nat) : Nat := A026741 n / A051712 (n + 1)

theorem b_sub (n : Nat) :
    b (n + 1) - b (n + 2) =
      Rat.divInt ((n * (n + 3) : Nat) : Int) ((((n + 2) * (n + 3) * (n + 4)) * (n + 3) : Nat) : Int) := by
  unfold b
  rw [Rat.divInt_sub_divInt _ _ (by norm_cast)
    (by norm_cast)]
  congr 1
  · push_cast; grind
  · push_cast; grind

theorem gcd24 (n : Nat) : Nat.gcd ((n + 2) * (n + 3) * (n + 4)) n = Nat.gcd 24 n := by
  have : (n + 2) * (n + 3) * (n + 4) = 24 + (n * n + 9 * n + 26) * n := by
    grind
  rw [this, Nat.gcd_add_mul_right_left]

theorem A051712_succ {n : Nat} (hn : 1 ≤ n) : A051712 (n + 1) = n / Nat.gcd n 24 := by
  unfold A051712
  rw [show n + 1 + 1 = n + 2 by omega, b_sub, Rat.num_divInt,
    Int.sign_natCast_of_ne_zero (by
      apply Nat.ne_of_gt; apply Nat.mul_pos <;> (try apply Nat.mul_pos) <;> (try apply Nat.mul_pos) <;> omega),
    Int.one_mul, Int.gcd_natCast_natCast, ← Int.natCast_ediv, Int.natAbs_natCast,
    Nat.gcd_mul_right, gcd24, Nat.gcd_comm 24 n, Nat.mul_comm n (n + 3),
    Nat.mul_comm (Nat.gcd n 24) (n + 3), Nat.mul_div_mul_left _ _ (by omega)]

theorem A164848_closed {n : Nat} (hn : 1 ≤ n) :
    A164848 n = if n % 2 = 1 then Nat.gcd n 24 else Nat.gcd n 24 / 2 := by
  unfold A164848 A026741
  rw [A051712_succ hn]
  obtain ⟨t, ht⟩ := Nat.gcd_dvd_left n 24
  have h2g : n % 2 = 0 → 2 ∣ Nat.gcd n 24 :=
    fun h => Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) (by decide)
  generalize Nat.gcd n 24 = g at ht h2g ⊢
  have ht0 : 0 < t := by
    apply Nat.pos_of_ne_zero; intro h; rw [h, Nat.mul_zero] at ht; omega
  have hg0 : 0 < g := by
    apply Nat.pos_of_ne_zero; intro h; rw [h, Nat.zero_mul] at ht; omega
  have hnt : n / g = t := Nat.div_eq_of_eq_mul_left hg0 (by rw [Nat.mul_comm]; exact ht)
  rw [hnt]
  split
  · exact Nat.div_eq_of_eq_mul_left ht0 ht
  · obtain ⟨s, rfl⟩ := h2g (by omega)
    have hn2 : n / 2 = s * t := by
      rw [ht, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
    rw [hn2, Nat.mul_div_cancel _ ht0, Nat.mul_div_cancel_left _ (by decide)]

/-- The conjecture: a(n + 24) = a(n) for every n ≥ 1. -/
theorem A164848_periodic {n : Nat} (hn : 1 ≤ n) : A164848 (n + 24) = A164848 n := by
  rw [A164848_closed hn, A164848_closed (by omega), Nat.gcd_add_self_left,
    show (n + 24) % 2 = n % 2 by omega]

/-- First 48 terms from the definition (data line of the OEIS entry). -/
theorem A164848_terms :
    (List.range 48).map (fun k => A164848 (k + 1)) =
      [1,1,3,2,1,3,1,4,3,1,1,6,1,1,3,4,1,3,1,2,3,1,1,12,
       1,1,3,2,1,3,1,4,3,1,1,6,1,1,3,4,1,3,1,2,3,1,1,12] := by
  have h : (List.range 48).map (fun k => A164848 (k + 1)) =
      (List.range 48).map (fun k => if (k + 1) % 2 = 1 then Nat.gcd (k + 1) 24
        else Nat.gcd (k + 1) 24 / 2) :=
    List.map_congr_left (fun k _ => A164848_closed (by omega))
  rw [h]; decide
