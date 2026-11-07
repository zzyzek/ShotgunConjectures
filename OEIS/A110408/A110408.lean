/-
OEIS A110408: smallest prime which is the repeated reverse concatenation of n
followed by n (ending in n), n = 1, 3, 7, 9 (mod 10), or 0 if no such prime exists.
The candidates are N_k(n) = rev(n) rev(n) ... rev(n) n (k >= 1 copies of rev(n)).
Conjecture (entry): a(n) = 0 iff n is a palindromic prime = 1,3,7,9 (mod 10)
and/or n = 0 (mod 3).

Checked here (core Lean, no imports).  `rep r d k` is r written k times in
blocks of d digits; `cand r n d k = rep r d k * 10^d + n` is N_k when r = rev n
and n has d digits.
* `palin_composite`: if rev n = n and n > 1 then n ∣ N_k and n < N_k for every
  k ≥ 1; so no candidate is prime and a(n) = 0 for every palindrome n > 1.
* `three_composite`: if 3 ∣ n and rev n ≡ n (mod 3) (true for every n: digit sums)
  then 3 ∣ N_k and 3 < N_k.
* `A110408_121`: 121 has 3 digits, rev 121 = 121, 121 ≡ 1 (mod 10), 3 ∤ 121 and
  121 = 11 * 11 is not prime; with `palin_composite` this gives a(121) = 0 against
  the "only if" direction.  (Also 161 = 7*23, 323, 343, 707, 767, 949, ...)
* `rep3_mod`: for 3-digit blocks, rep r 3 k ≡ 0 (k even) or r (k odd) mod 1001
  (10^3 ≡ -1 mod 1001).
* `A110408_119`: rev 119 = 911, 119 = 7 * 17, 3 ∤ 119, 119 ≡ 9 (mod 10) is not a
  palindrome; every N_k(119) (k ≥ 1) is divisible by 7 (k even) or 11 (k odd) and
  exceeds 11, so a(119) = 0 although 119 is neither a palindromic prime nor a
  multiple of 3.  (Same for every 3-digit n divisible by 7 or 13: n - rev n is a
  multiple of 99.)
Not checked here: rev n ≡ n (mod 3) for general n (digit-sum argument), and the
open question whether a(n) > 0 for every non-palindromic n with 3 ∤ n.
-/

def rep (r d : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => rep r d k * 10 ^ d + r

def cand (r n d k : Nat) : Nat := rep r d k * 10 ^ d + n

def revDigits (n : Nat) : Nat := (Nat.toDigits 10 n).reverse.foldl (fun a c => 10 * a + (c.toNat - 48)) 0

theorem rep_dvd (r d : Nat) (m : Nat) (h : m ∣ r) : ∀ k, m ∣ rep r d k
  | 0 => Nat.dvd_zero m
  | k + 1 => Nat.dvd_add (Nat.dvd_trans (rep_dvd r d m h k) (Nat.dvd_mul_right _ _)) h

theorem rep_pos (r d : Nat) (hr : 0 < r) : ∀ k, 0 < k → 0 < rep r d k
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | k + 1, _ => by
    show 0 < rep r d k * 10 ^ d + r
    omega

theorem palin_composite (n d k : Nat) (hn : 1 < n) (hk : 1 ≤ k) :
    n ∣ cand n n d k ∧ n < cand n n d k := by
  constructor
  · exact Nat.dvd_add (Nat.dvd_trans (rep_dvd n d n (Nat.dvd_refl n) k) (Nat.dvd_mul_right _ _))
      (Nat.dvd_refl n)
  · have h1 := rep_pos n d (by omega) k hk
    have h2 : 0 < 10 ^ d := Nat.pos_of_ne_zero (by simp)
    have h3 : 0 < rep n d k * 10 ^ d := Nat.mul_pos h1 h2
    unfold cand; omega

theorem rep_mod3 (r d : Nat) : ∀ k, rep r d k % 3 = (k * r) % 3
  | 0 => by simp [rep]
  | k + 1 => by
    show (rep r d k * 10 ^ d + r) % 3 = ((k + 1) * r) % 3
    have hp : 10 ^ d % 3 = 1 := by
      induction d with
      | zero => rfl
      | succ e ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
    rw [Nat.add_mod, Nat.mul_mod, hp, rep_mod3 r d k, Nat.add_mul, Nat.one_mul,
      Nat.mul_one, Nat.mod_mod, ← Nat.add_mod]

theorem three_composite (r n d k : Nat) (h3 : 3 ∣ n) (hr : r % 3 = n % 3) (hn : 0 < n)
    (hrp : 0 < r) (hk : 1 ≤ k) :
    3 ∣ cand r n d k ∧ 3 < cand r n d k := by
  have h10 : 10 ^ d % 3 = 1 := by
    induction d with
    | zero => rfl
    | succ e ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
  constructor
  · apply Nat.dvd_of_mod_eq_zero
    unfold cand
    have hr0 : r % 3 = 0 := by rw [hr]; exact Nat.mod_eq_zero_of_dvd h3
    have hn0 : n % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
    rw [Nat.add_mod, Nat.mul_mod, h10, rep_mod3, Nat.mul_mod k r, hr0, hn0]
    simp
  · have h1 := rep_pos r d hrp k hk
    have h2 : 0 < 10 ^ d := Nat.pos_of_ne_zero (by simp)
    have hn3 : 3 ≤ n := Nat.le_of_dvd hn h3
    have h4 : 1 ≤ rep r d k * 10 ^ d := Nat.mul_pos h1 h2
    unfold cand; omega

theorem A110408_121 :
    revDigits 121 = 121 ∧ (Nat.toDigits 10 121).length = 3 ∧ 121 % 10 = 1 ∧
    121 % 3 ≠ 0 ∧ 121 = 11 * 11 := by decide

theorem A110408_121_zero (k : Nat) (hk : 1 ≤ k) :
    121 ∣ cand 121 121 3 k ∧ 121 < cand 121 121 3 k :=
  palin_composite 121 3 k (by decide) hk

theorem rep3_mod (r : Nat) : ∀ k, rep r 3 (2 * k) % 1001 = 0 ∧ rep r 3 (2 * k + 1) % 1001 = r % 1001
  | 0 => by simp [rep]
  | k + 1 => by
    obtain ⟨_, h1⟩ := rep3_mod r k
    have e1 : rep r 3 (2 * (k + 1)) = rep r 3 (2 * k + 1) * 10 ^ 3 + r := rfl
    have e2 : rep r 3 (2 * (k + 1) + 1) = rep r 3 (2 * (k + 1)) * 10 ^ 3 + r := rfl
    have h0 : rep r 3 (2 * (k + 1)) % 1001 = 0 := by
      rw [e1]; omega
    exact ⟨h0, by rw [e2]; omega⟩

theorem A110408_119 (k : Nat) (hk : 1 ≤ k) :
    (7 ∣ cand 911 119 3 k ∨ 11 ∣ cand 911 119 3 k) ∧ 11 < cand 911 119 3 k := by
  have hpos := rep_pos 911 3 (by decide) k hk
  unfold cand
  have hk2 : k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 := by omega
  rcases hk2 with hj | hj
  · rw [hj] at hpos ⊢
    have h := (rep3_mod 911 (k / 2)).1
    constructor
    · left; omega
    · omega
  · rw [hj] at hpos ⊢
    have h := (rep3_mod 911 (k / 2)).2
    constructor
    · right; omega
    · omega

theorem A110408_119_facts :
    revDigits 119 = 911 ∧ (Nat.toDigits 10 119).length = 3 ∧ 119 % 10 = 9 ∧
    119 % 3 ≠ 0 ∧ 119 = 7 * 17 ∧ revDigits 119 ≠ 119 := by decide
