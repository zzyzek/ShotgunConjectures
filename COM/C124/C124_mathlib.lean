import OpenProblemsLib

/-
COM-C124 (Mathlib). Coman's conjecture 124: every 3-Carmichael number C (a Carmichael number
with exactly three prime factors) divisible by 5 is p(q − 2^n) with p a prime factor of C
other than 5, q prime and n ≥ 1. README result: true; the only such C are 1105, 2465 and
10585, and 1105 = 13(89 − 2²), 2465 = 17(149 − 2²), 10585 = 29(367 − 2).

Main theorem `C124_main`: for every Carmichael number C (Mathlib `Nat.IsCarmichael`) with
`C.primeFactors.card = 3` and 5 ∣ C: C ∈ {1105, 2465, 10585}, and C = p(q − 2^n) for some
prime p ∣ C with p ≠ 5, prime q and n ≥ 1.
Proof: C is squarefree (Mathlib), so C = 5pq with primes p < q other than 5. Korselt's
criterion in the necessary direction (Mathlib `Nat.IsCarmichael.prime_sub_one_dvd`):
q − 1 ∣ 5pq − 1 gives 5p − 1 = h(q − 1) with h ≤ 4; p − 1 ∣ 5q − 1 and the core-Lean identity
`key` of `C124.lean` (copied below in namespace `Core`) give p − 1 ∣ 20 + 4h, so p ≤ 37 and
q < 200; a kernel enumeration (`enum_small`, primality as trial division) over these finitely
many (p, h, q) leaves the three numbers.

Outside Lean: nothing. (Generated from certificate/C124_mathlib.lean.in by
tools/lean_expand.py.)
-/

open OpenProblemsLib

/-! ### Core-Lean facts, copied verbatim from `C124.lean` -/
namespace Core
  /-! ### Shared core-Lean toolkit (copied into each COM file; no imports) -/

  /-- Modular exponentiation by squaring, with fuel (64 bits suffice below 2^64). -/
  def powMod (b e m : Nat) : Nat → Nat
    | 0 => 1 % m
    | fuel + 1 =>
      if e = 0 then 1 % m
      else
        let h := powMod b (e / 2) m fuel
        let h2 := h * h % m
        if e % 2 = 1 then h2 * b % m else h2

  theorem powMod_eq (b m : Nat) : ∀ (fuel e : Nat), e < 2 ^ fuel → powMod b e m fuel = b ^ e % m
    | 0, e, h => by
      have : e = 0 := by simp at h; omega
      subst this; simp [powMod]
    | fuel + 1, e, h => by
      by_cases he : e = 0
      · subst he; simp [powMod]
      · have ih := powMod_eq b m fuel (e / 2) (by rw [Nat.pow_succ] at h; omega)
        have hsq : b ^ (2 * (e / 2)) = b ^ (e / 2) * b ^ (e / 2) := by
          rw [Nat.two_mul, Nat.pow_add]
        have hmm : b ^ (e / 2) % m * (b ^ (e / 2) % m) % m = b ^ (e / 2) * b ^ (e / 2) % m :=
          (Nat.mul_mod _ _ _).symm
        simp only [powMod, he, ih]
        by_cases ho : e % 2 = 1
        · have hs : e = 2 * (e / 2) + 1 := by omega
          simp only [ho, ite_true, ite_false]
          rw [hmm, Nat.mod_mul_mod]
          conv => rhs; rw [hs, Nat.pow_succ, hsq]
        · have hs : e = 2 * (e / 2) := by omega
          simp only [ho, ite_false]
          rw [hmm]
          conv => rhs; rw [hs, hsq]

  /-- `b ^ e % m` computed by squaring (valid for e < 2^128). -/
  theorem pow_mod_fast (b e m : Nat) (he : e < 2 ^ 128) : b ^ e % m = powMod b e m 128 :=
    (powMod_eq b m 128 e he).symm

  /-- Bounded check: `allLt P n` iff `P i` for every i < n (kernel-friendly, linear). -/
  def allLt (P : Nat → Bool) (n : Nat) : Bool :=
    Nat.rec (motive := fun _ => Bool) true (fun i r => P i && r) n

  theorem allLt_spec (P : Nat → Bool) : ∀ n, allLt P n = true → ∀ i, i < n → P i = true
    | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
    | n + 1, h, i, hi => by
      have h' : (P n && allLt P n) = true := h
      rw [Bool.and_eq_true] at h'
      by_cases hin : i = n
      · subst hin; exact h'.1
      · exact allLt_spec P n h'.2 i (by omega)

  theorem allLt_of (P : Nat → Bool) : ∀ n, (∀ i, i < n → P i = true) → allLt P n = true
    | 0, _ => rfl
    | n + 1, h => by
      show (P n && allLt P n) = true
      rw [Bool.and_eq_true]
      exact ⟨h n (by omega), allLt_of P n (fun i hi => h i (by omega))⟩

  def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

  /-- Trial division: no k with 2 ≤ k < B divides p, and p < B * B. -/
  theorem prime_of_trial (p B : Nat) (h2 : 2 ≤ p) (hB : p < B * B)
      (tr : ∀ k, 2 ≤ k → k < B → p % k ≠ 0) : IsPrime p := by
    refine ⟨h2, fun d hd => ?_⟩
    obtain ⟨e, he⟩ := hd
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h; simp at he; omega
      · exact h
    have he0 : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · subst h; simp at he; omega
      · exact h
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    by_cases he1 : e = 1
    · subst he1; simp at he; exact Or.inr he.symm
    exfalso
    rcases Nat.le_total d e with hle | hle
    · have hdB : d < B := by
        apply Nat.lt_of_not_le; intro hc
        have : B * B ≤ d * e := Nat.mul_le_mul hc (Nat.le_trans hc hle)
        omega
      exact tr d (by omega) hdB (by rw [he]; simp)
    · have heB : e < B := by
        apply Nat.lt_of_not_le; intro hc
        have : B * B ≤ d * e := Nat.mul_le_mul (Nat.le_trans hc hle) hc
        omega
      exact tr e (by omega) heB (by rw [he]; simp)

  /-- `noDivRange p a n`: no k with a ≤ k < a + n divides p. -/
  def noDivRange (p a n : Nat) : Bool := allLt (fun i => p % (a + i) != 0) n

  theorem noDivRange_spec (p a n : Nat) (h : noDivRange p a n = true) :
      ∀ k, a ≤ k → k < a + n → p % k ≠ 0 := by
    intro k h1 h2
    have := allLt_spec _ n h (k - a) (by omega)
    simp only [bne_iff_ne, ne_eq] at this
    have e : a + (k - a) = k := by omega
    rw [e] at this; exact this

  /-- Trial division certificate (one range). -/
  theorem prime_cert (p B : Nat) (h2 : 2 ≤ p) (hB : p < B * B)
      (ht : noDivRange p 2 (B - 2) = true) : IsPrime p :=
    prime_of_trial p B h2 hB (fun k hk1 hk2 => noDivRange_spec p 2 (B - 2) ht k hk1 (by omega))

  theorem not_prime_of_dvd (n d : Nat) (h1 : 2 ≤ d) (h2 : d < n) (h : n % d = 0) : ¬ IsPrime n := by
    intro ⟨_, hp⟩
    rcases hp d (Nat.dvd_of_mod_eq_zero h) with h' | h' <;> omega

  /-- Base-2 Fermat pseudoprime (Poulet number). -/
  def Poulet (n : Nat) : Prop := 2 ≤ n ∧ ¬ IsPrime n ∧ 2 ^ (n - 1) % n = 1

  /-- Carmichael number: composite, a^(n-1) ≡ 1 (mod n) for every a coprime to n. -/
  def Carmichael (n : Nat) : Prop :=
    2 ≤ n ∧ ¬ IsPrime n ∧ ∀ a, Nat.gcd a n = 1 → a ^ (n - 1) % n = 1

  /-- Korselt data: the list multiplies to n, has no repeats, and p - 1 ∣ n - 1 for each entry.
      With every entry prime this is Korselt's criterion (stated outside Lean). -/
  def korseltB (n : Nat) (fs : List Nat) : Bool :=
    fs.foldl (· * ·) 1 == n && fs.eraseDups.length == fs.length &&
    fs.all (fun p => (n - 1) % (p - 1) == 0)

  /-- Brute-force Carmichael check over all bases below n (small n only). -/
  theorem carmichael_of_check (n : Nat) (h2 : 2 ≤ n) (hc : ¬ IsPrime n) (hn : n - 1 < 2 ^ 64)
      (h : allLt (fun a => Nat.gcd a n != 1 || powMod a (n - 1) n 64 == 1) n = true) :
      Carmichael n := by
    refine ⟨h2, hc, fun a ha => ?_⟩
    have hlt : a % n < n := Nat.mod_lt _ (by omega)
    have := allLt_spec _ n h (a % n) hlt
    have hg : Nat.gcd (a % n) n = 1 := by
      rw [← Nat.gcd_rec, Nat.gcd_comm]; exact ha
    simp only [hg, bne_self_eq_false, Bool.false_or, beq_iff_eq] at this
    rw [Nat.pow_mod, ← powMod_eq _ _ 64 _ hn]; exact this

  /-- b^n mod q depends only on n mod o when b^o ≡ 1 (mod q). -/
  theorem pow_period (b q o n : Nat) (ho : b ^ o % q = 1) : b ^ n % q = b ^ (n % o) % q := by
    have h := Nat.div_add_mod n o
    conv => lhs; rw [← h, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, ho, Nat.one_pow]
    have hq : q ≠ 1 := by
      intro h1; rw [h1, Nat.mod_one] at ho; exact absurd ho (by decide)
    cases q with
    | zero => simp
    | succ q' =>
      have : 1 % (q' + 1) = 1 := Nat.mod_eq_of_lt (by omega)
      rw [this, Nat.one_mul, Nat.mod_mod]

  /-- (n-1)^k mod n alternates between 1 and n-1. -/
  theorem pow_pred_mod (n : Nat) (hn : 2 ≤ n) : ∀ k, (n - 1) ^ k % n = if k % 2 = 0 then 1 else n - 1
    | 0 => by simp; exact Nat.mod_eq_of_lt (by omega)
    | k + 1 => by
      rw [Nat.pow_succ, Nat.mul_mod, pow_pred_mod n hn k]
      have hsq : (n - 1) * (n - 1) = n * (n - 2) + 1 := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
        show (m + 1) * (m + 1) = (m + 2) * m + 1
        simp only [Nat.add_mul, Nat.mul_add]; omega
      have hm : (n - 1) % n = n - 1 := Nat.mod_eq_of_lt (by omega)
      have h1 : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
      by_cases hk : k % 2 = 0
      · have : (k + 1) % 2 ≠ 0 := by omega
        simp only [hk, ite_true, this, ite_false, hm, Nat.one_mul]
      · have : (k + 1) % 2 = 0 := by omega
        simp only [hk, ite_false, this, ite_true, hm, hsq, Nat.mul_add_mod, h1]

  /-- Every Carmichael number is odd. -/
  theorem carmichael_odd (n : Nat) (h : Carmichael n) : n % 2 = 1 := by
    obtain ⟨h2, hp, hc⟩ := h
    have h3 : 3 ≤ n := by
      apply Nat.lt_of_not_le; intro hle
      apply hp
      have : n = 2 := by omega
      subst this; exact ⟨by decide, fun d hd => by
        have := Nat.le_of_dvd (by decide) hd
        have : d ≠ 0 := by rintro rfl; simp at hd
        omega⟩
    refine Decidable.byContradiction fun hne => ?_
    have hev : n % 2 = 0 := by omega
    have hg : Nat.gcd (n - 1) n = 1 := by
      rw [Nat.gcd_rec]
      have e : n = (n - 1) + 1 := by omega
      have : n % (n - 1) = 1 := by
        conv => lhs; arg 1; rw [e]
        rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt (by omega)
      rw [this, Nat.gcd_one_left]
    have := hc (n - 1) hg
    rw [pow_pred_mod n h2] at this
    have : (n - 1) % 2 ≠ 0 := by omega
    simp_all

  /-- A Carmichael number is a base-2 Fermat pseudoprime. -/
  theorem carmichael_poulet (n : Nat) (h : Carmichael n) : 2 ^ (n - 1) % n = 1 := by
    have hodd := carmichael_odd n h
    apply h.2.2 2
    rw [Nat.gcd_rec]
    have : n % 2 = 1 := hodd
    rw [this, Nat.gcd_one_left]

  /-- Bounded factor-pair search: if no divisor x of N (x ≤ N) has x, N/x ≥ lo and
      both ≡ r (mod m), then N has no such factorization x * y. -/
  theorem no_pair (N m r lo : Nat) (hN : 0 < N)
      (h : allLt (fun x => N % x != 0 || x < lo || N / x < lo || x % m != r || (N / x) % m != r)
        (N + 1) = true) :
      ∀ x y, x * y = N → lo ≤ x → lo ≤ y → x % m = r → y % m = r → False := by
    intro x y hxy hx hy hxr hyr
    have hx0 : 0 < x := by
      rcases Nat.eq_zero_or_pos x with h0 | h0
      · subst h0; simp at hxy; omega
      · exact h0
    have hxN : x ≤ N := by
      rw [← hxy]; exact Nat.le_mul_of_pos_right x (by
        rcases Nat.eq_zero_or_pos y with h0 | h0
        · subst h0; simp at hxy; omega
        · exact h0)
    have hd : N / x = y := by rw [← hxy, Nat.mul_div_cancel_left _ hx0]
    have hm : N % x = 0 := by rw [← hxy]; simp
    have := allLt_spec _ (N + 1) h x (by omega)
    simp only [hm, hd, hxr, hyr, bne_self_eq_false, Bool.false_or, Bool.or_false] at this
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    omega

  theorem cancel_left (p N X Y : Nat) (hp : 0 < p) (h : p * N = p * X * Y) : X * Y = N := by
    rw [Nat.mul_assoc] at h; exact (Nat.eq_of_mul_eq_mul_left hp h).symm

  /-- Chinese remainder for the residue 1. -/
  theorem crt_one (a b x : Nat) (cop : Nat.Coprime a b) (hx : 1 ≤ x)
      (ha : x % a = 1 % a) (hb : x % b = 1 % b) : x % (a * b) = 1 % (a * b) := by
    have da : a ∣ x - 1 := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq ha)
    have db : b ∣ x - 1 := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hb)
    have hab := Nat.Coprime.mul_dvd_of_dvd_of_dvd cop da db
    have e : x = (x - 1) + 1 := by omega
    have h0 : (x - 1) % (a * b) = 0 := Nat.mod_eq_zero_of_dvd hab
    rw [e, Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod]

  /-- Odd numbers two apart are coprime. -/
  theorem coprime_odd2 (a : Nat) (ha : a % 2 = 1) : Nat.Coprime a (a + 2) := by
    show Nat.gcd a (a + 2) = 1
    have g1 := Nat.gcd_dvd_left a (a + 2)
    have g2 := Nat.gcd_dvd_right a (a + 2)
    have h2 : Nat.gcd a (a + 2) ∣ 2 := (Nat.dvd_add_right g1).mp g2
    have hle := Nat.le_of_dvd (by decide) h2
    have hpos : 0 < Nat.gcd a (a + 2) := Nat.gcd_pos_of_pos_left _ (by omega)
    have hne : Nat.gcd a (a + 2) ≠ 2 := by
      intro h; rw [h] at g1; have := Nat.mod_eq_zero_of_dvd g1; omega
    omega

  /-- Euclid's lemma for `IsPrime`. -/
  theorem prime_dvd_mul (q a b : Nat) (hq : IsPrime q) (h : q ∣ a * b) : q ∣ a ∨ q ∣ b := by
    by_cases ha : q ∣ a
    · exact Or.inl ha
    · right
      have hg : Nat.gcd q a = 1 := by
        rcases hq.2 _ (Nat.gcd_dvd_left q a) with h1 | h1
        · exact h1
        · exact absurd (h1 ▸ Nat.gcd_dvd_right q a) ha
      exact Nat.Coprime.dvd_of_dvd_mul_left hg h

  theorem prime_dvd_prime (q p : Nat) (hq : IsPrime q) (hp : IsPrime p) (h : q ∣ p) : q = p := by
    rcases hp.2 q h with h1 | h1
    · have := hq.1; omega
    · exact h1

  /-- Order argument: if b^o ≡ 1 (mod q) and no smaller positive r has b^r ≡ 1, then
      b^x ≡ 1 (mod q) forces o ∣ x. -/
  theorem ord_dvd (b q o x : Nat) (ho0 : 0 < o) (ho : b ^ o % q = 1)
      (hmin : allLt (fun r => r == 0 || b ^ r % q != 1) o = true) (hx : b ^ x % q = 1) : x % o = 0 := by
    rw [pow_period b q o x ho] at hx
    have := allLt_spec _ o hmin (x % o) (Nat.mod_lt _ ho0)
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
    rcases this with h | h
    · exact h
    · exact absurd hx h

  /-- A base-2 congruence mod n descends to any divisor q of n. -/
  theorem pow_mod_dvd (x n q : Nat) (h : x % n = 1) (hq : q ∣ n) (hq1 : 2 ≤ q) : x % q = 1 := by
    rw [← Nat.mod_mod_of_dvd x hq, h]; exact Nat.mod_eq_of_lt (by omega)

  theorem noDivRange_of_prime (x n : Nat) (hx : IsPrime x) (hn : 2 + n ≤ x) : noDivRange x 2 n = true := by
    apply allLt_of; intro i hi
    simp only [bne_iff_ne, ne_eq]
    intro h0
    rcases hx.2 (2 + i) (Nat.dvd_of_mod_eq_zero h0) with h | h <;> omega

  /-- `compositeB x B`: x < 2, or x has a divisor in [2, min x B). Sound for `¬ IsPrime`. -/
  def compositeB (x B : Nat) : Bool := x < 2 || !(noDivRange x 2 (min x B - 2))

  theorem compositeB_spec (x B : Nat) (h : compositeB x B = true) : ¬ IsPrime x := by
    intro hp
    have h2 := hp.1
    simp only [compositeB, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    rcases h with h | h
    · omega
    · rw [noDivRange_of_prime x _ hp (by omega)] at h; exact absurd h (by decide)

  /-- A prime dividing q^k divides q. -/
  theorem prime_dvd_pow (r q : Nat) (hr : IsPrime r) : ∀ k, r ∣ q ^ k → r ∣ q
    | 0, h => by
      rw [Nat.pow_zero] at h
      have := Nat.le_of_dvd (by decide) h; have := hr.1; omega
    | k + 1, h => by
      rw [Nat.pow_succ] at h
      rcases prime_dvd_mul r _ _ hr h with h1 | h1
      · exact prime_dvd_pow r q hr k h1
      · exact h1

  def IsPrimePow (m : Nat) : Prop := ∃ q k, IsPrime q ∧ 1 ≤ k ∧ m = q ^ k

  /-- Two distinct primes dividing m rule out m being a prime power. -/
  theorem not_prime_pow (m r s : Nat) (hr : IsPrime r) (hs : IsPrime s) (hne : r ≠ s)
      (hrm : r ∣ m) (hsm : s ∣ m) : ¬ IsPrimePow m := by
    rintro ⟨q, k, hq, hk, rfl⟩
    have h1 := prime_dvd_prime r q hr hq (prime_dvd_pow r q hr k hrm)
    have h2 := prime_dvd_prime s q hs hq (prime_dvd_pow s q hs k hsm)
    exact hne (h1.trans h2.symm)

  /-- A coprime base with a^(n-1) ≢ 1 (mod n) shows n is not a Carmichael number. -/
  theorem not_carmichael (n a : Nat) (hg : Nat.gcd a n = 1) (hn : n - 1 < 2 ^ 128)
      (hp : powMod a (n - 1) n 128 ≠ 1) : ¬ Carmichael n := by
    intro h; apply hp; rw [← pow_mod_fast _ _ _ hn]; exact h.2.2 a hg

  /-! ### Problem-specific checks -/

  theorem key (p q h : Nat) (hq : 1 ≤ q) (hh : h * (q - 1) = 5 * p - 1) (hp : 1 ≤ p) :
      h * (5 * q - 1) = 25 * (p - 1) + 20 + 4 * h := by
    obtain ⟨e, rfl⟩ : ∃ e, q = e + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hh
    have : h * (5 * (e + 1) - 1) = 5 * (h * e) + 4 * h := by
      rw [show 5 * (e + 1) - 1 = 5 * e + 4 by omega]; grind
    omega
  def primeB (x : Nat) : Bool := !(compositeB x 200)
  def enum : List Nat := ((List.range 38).filter (fun p => primeB p && p != 5)).flatMap (fun p =>
    ((List.range 5).filter (fun h => 1 ≤ h && (5 * p - 1) % h == 0)).filterMap (fun h =>
      let q := (5 * p - 1) / h + 1
      if q > p && q != 5 && primeB q && korseltB (5 * p * q) [5, p, q] then some (5 * p * q) else none))
  theorem enum_eq : enum.eraseDups = [1105, 2465, 10585] := by decide +kernel
  theorem prime_89 : IsPrime 89 := prime_cert 89 10 (by decide) (by decide) (by decide +kernel)
  theorem prime_149 : IsPrime 149 := prime_cert 149 13 (by decide) (by decide) (by decide +kernel)
  theorem prime_367 : IsPrime 367 := prime_cert 367 20 (by decide) (by decide) (by decide +kernel)
  theorem reps : 1105 = 13 * (89 - 2 ^ 2) ∧ 2465 = 17 * (149 - 2 ^ 2) ∧ 10585 = 29 * (367 - 2 ^ 1) := by decide
end Core

/-- Bool form of the finite enumeration (kernel-evaluated). -/
def enumB : Bool :=
  Core.allLt (fun p => Core.allLt (fun h => Core.allLt (fun q =>
    !(h * (q - 1) == 5 * p - 1) || !(decide (2 ≤ p)) || !(Core.noDivRange p 2 (p - 2)) ||
    !(Core.noDivRange q 2 (q - 2)) || p == 5 || q == 5 || !(decide (p < q)) ||
    !((5 * p * q - 1) % (p - 1) == 0) || !((5 * p * q - 1) % (q - 1) == 0) ||
    !((5 * p * q - 1) % 4 == 0) ||
    (5 * p * q == 1105 || 5 * p * q == 2465 || 5 * p * q == 10585)) 200) 5) 38

theorem enumB_eq : enumB = true := by decide +kernel

theorem enum_small : ∀ p, p < 38 → ∀ h, h < 5 → ∀ q, q < 200 → h * (q - 1) = 5 * p - 1 →
    2 ≤ p → Core.noDivRange p 2 (p - 2) = true → Core.noDivRange q 2 (q - 2) = true → p ≠ 5 →
    q ≠ 5 → p < q → (5 * p * q - 1) % (p - 1) = 0 →
    (5 * p * q - 1) % (q - 1) = 0 → (5 * p * q - 1) % 4 = 0 →
    5 * p * q = 1105 ∨ 5 * p * q = 2465 ∨ 5 * p * q = 10585 := by
  intro p hp h hh q hq e p2 tp tq p5 q5 pq m1 m2 m3
  have := Core.allLt_spec _ _ (Core.allLt_spec _ _ (Core.allLt_spec _ _ enumB_eq p hp) h hh) q hq
  simp only [e, p2, tp, tq, p5, q5, pq, m1, m2, m3, beq_self_eq_true, Bool.not_true, Bool.false_or,
    beq_iff_eq, decide_true, Bool.or_eq_true] at this
  simpa [p5, q5, or_assoc] using this

theorem trial_of_prime (p : ℕ) (hp : p.Prime) : Core.noDivRange p 2 (p - 2) = true :=
  Core.noDivRange_of_prime p _ (Nat.prime_def.mp hp) (by have := hp.two_le; omega)

theorem sorted (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp5 : p ≠ 5) (hq5 : q ≠ 5) (hpq : p < q)
    (h : (5 * p * q).IsCarmichael) : 5 * p * q = 1105 ∨ 5 * p * q = 2465 ∨ 5 * p * q = 10585 := by
  have hp2 := hp.two_le
  have kq := korselt_necessary h hq (Dvd.intro_left _ rfl)
  have kp := korselt_necessary h hp (Dvd.intro (5 * q) (by ring))
  have k5 : 4 ∣ 5 * p * q - 1 := by
    simpa using korselt_necessary h Nat.prime_five (Dvd.intro (p * q) (by ring))
  -- q - 1 ∣ 5p - 1
  have e1 : 5 * p * q - 1 = (q - 1) * (5 * p) + (5 * p - 1) := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : 5 * p * (q' + 1) = 5 * p * q' + 5 * p := by ring
    rw [this, mul_comm q' (5 * p)]
    omega
  have dq : q - 1 ∣ 5 * p - 1 := by
    rw [e1] at kq; exact (Nat.dvd_add_right (Dvd.intro _ rfl)).mp kq
  obtain ⟨h0, hh⟩ := dq
  have hh5 : h0 < 5 := by
    by_contra hge
    have : (q - 1) * 5 ≤ (q - 1) * h0 := Nat.mul_le_mul_left _ (by omega)
    omega
  -- p - 1 ∣ 5q - 1
  have e2 : 5 * p * q - 1 = (p - 1) * (5 * q) + (5 * q - 1) := by
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : 5 * (p' + 1) * q = p' * (5 * q) + 5 * q := by ring
    rw [this]
    omega
  have dp : p - 1 ∣ 5 * q - 1 := by
    rw [e2] at kp; exact (Nat.dvd_add_right (Dvd.intro _ rfl)).mp kp
  have hkey := Core.key p q h0 (by omega) (by rw [mul_comm]; exact hh.symm) (by omega)
  have dp2 : p - 1 ∣ 20 + 4 * h0 := by
    have : p - 1 ∣ h0 * (5 * q - 1) := Dvd.dvd.mul_left dp _
    rw [hkey, add_assoc] at this
    exact (Nat.dvd_add_right (Dvd.intro_left 25 rfl)).mp this
  have hp38 : p < 38 := by
    have := Nat.le_of_dvd (by omega) dp2
    omega
  have hq200 : q < 200 := by
    rcases Nat.eq_zero_or_pos h0 with h00 | h0pos
    · subst h00; omega
    · have : (q - 1) * 1 ≤ (q - 1) * h0 := Nat.mul_le_mul_left _ h0pos
      omega
  exact enum_small p hp38 h0 hh5 q hq200 (by rw [mul_comm]; exact hh.symm) hp2 (trial_of_prime p hp)
    (trial_of_prime q hq) hp5 hq5 hpq
    (Nat.mod_eq_zero_of_dvd kp) (Nat.mod_eq_zero_of_dvd kq) (Nat.mod_eq_zero_of_dvd k5)

theorem C124_main (C : ℕ) (h : C.IsCarmichael) (h3 : C.primeFactors.card = 3) (h5 : 5 ∣ C) :
    (C = 1105 ∨ C = 2465 ∨ C = 10585) ∧
    ∃ p q n : ℕ, p.Prime ∧ p ∣ C ∧ p ≠ 5 ∧ q.Prime ∧ 1 ≤ n ∧ C = p * (q - 2 ^ n) := by
  have hC0 : C ≠ 0 := by have := h.two_lt; omega
  have hprod : ∏ p ∈ C.primeFactors, p = C := Nat.prod_primeFactors_of_squarefree h.squarefree
  have h5mem : 5 ∈ C.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_five, h5, hC0⟩
  have hcard : (C.primeFactors.erase 5).card = 2 := by
    rw [Finset.card_erase_of_mem h5mem, h3]
  obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.mp hcard
  have hx : x ∈ C.primeFactors.erase 5 := by rw [hs]; simp
  have hy : y ∈ C.primeFactors.erase 5 := by rw [hs]; simp
  rw [Finset.mem_erase, Nat.mem_primeFactors] at hx hy
  have hC : C = 5 * x * y := by
    rw [← hprod, ← Finset.mul_prod_erase _ _ h5mem, hs, Finset.prod_pair hxy, mul_assoc]
  have hvals : C = 1105 ∨ C = 2465 ∨ C = 10585 := by
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · rw [hC] at h ⊢; exact sorted x y hx.2.1 hy.2.1 hx.1 hy.1 hlt h
    · rw [show C = 5 * y * x by rw [hC]; ring] at h ⊢
      exact sorted y x hy.2.1 hx.2.1 hy.1 hx.1 hlt h
  refine ⟨hvals, ?_⟩
  rcases hvals with rfl | rfl | rfl
  · exact ⟨13, 89, 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨17, 149, 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨29, 367, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
