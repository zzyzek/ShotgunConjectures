import OpenProblemsLib
import Mathlib.FieldTheory.Finite.Basic

/-
FAM-wieferich-composite (Mathlib). Question: is there a composite c with
2^(c-1) ≡ 1 (mod c^2) (a base-2 "Wieferich pseudoprime")?

Checked here:
* `wief_cofactor`: if 2^(c-1) ≡ 1 (mod c^2) and c = p^k * m with p prime, k ≥ 1, m ≥ 1,
  then 2^(p-1) ≡ 1 and 2^(m-1) ≡ 1 (mod p^(2k)).
* `wief_prime_factor`: every prime factor p of such c is a Wieferich prime.
* `wief_orderOf_dvd`: the order of 2 mod p^2 divides c - 1 (p prime, p ∣ c).
* `wief_sq_factor`: if p^2 ∣ c then 2^(p-1) ≡ 1 (mod p^4).
* `wief_no_1093_3511`: no c = 1093^a * 3511^b with a + b ≥ 2 is a solution.
* `sq_dvd_two_pow_1092`: the primes P with P^2 ∣ 2^1092 - 1 are 3, 7, 13, 1093
  (complete factorization of 2^1092 - 1, every prime factor Pratt-certified).
* `wief_no_1093_prime_power`: no c = 1093^a * P^k with P ≠ 1093 prime, a, k ≥ 1
  is a solution.

Not checked here: the factorization was found by PARI/GP (certificate/factor1092.gp);
Lean checks the product and the primality of every factor independently.
The PrimeGrid bound (any further Wieferich prime exceeds 2^64) is outside Lean.
-/

open OpenProblemsLib

/-- The cofactor lemma: for c = p^k * m, the order of 2 mod p^(2k) divides both p - 1 and
m - 1. -/
theorem wief_cofactor (c p k m : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hc : c = p ^ k * m) (h : 2 ^ (c - 1) ≡ 1 [MOD c ^ 2]) :
    2 ^ (p - 1) ≡ 1 [MOD p ^ (2 * k)] ∧ 2 ^ (m - 1) ≡ 1 [MOD p ^ (2 * k)] := by
  set n := p ^ (2 * k) with hn
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  have hc1 : 1 ≤ c := by rw [hc]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hndvd : n ∣ c ^ 2 := by
    rw [hn, hc, mul_pow, ← pow_mul, mul_comm k 2]
    exact Dvd.intro _ rfl
  have h1 : 2 ^ (c - 1) ≡ 1 [MOD n] := Nat.ModEq.of_dvd hndvd h
  -- p does not divide c - 1, since p divides c.
  --
  have hpc : p ∣ c := by
    rw [hc]
    exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) m
  have hcop : Nat.Coprime (c - 1) p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have : p ∣ c - (c - 1) := Nat.dvd_sub hpc hd
    rw [show c - (c - 1) = 1 by omega] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  -- p = 2 is impossible: 2^(c-1) would be ≡ 1 modulo an even number.
  --
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2n : 2 ∣ n := dvd_pow_self 2 (by omega)
    have h2 := Nat.ModEq.of_dvd h2n h1
    have hc2 : 2 ∣ c := hpc
    have hc2' : 1 ≤ c - 1 := by
      rcases hc2 with ⟨t, ht⟩
      omega
    unfold Nat.ModEq at h2
    rw [Nat.pow_mod, Nat.mod_self, zero_pow (by omega)] at h2
    simp at h2
  have hcop2 : Nat.Coprime 2 n := by
    rw [hn]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_primes Nat.prime_two hp]
    exact fun e => hp2 e.symm
  have h2 : 2 ^ (Nat.totient n) ≡ 1 [MOD n] := Nat.ModEq.pow_totient hcop2
  have htot : Nat.totient n = p ^ (2 * k - 1) * (p - 1) := by
    rw [hn, Nat.totient_prime_pow hp (by omega)]
  -- Move to ZMod n and combine the two exponents through their gcd.
  --
  have z1 : (2 : ZMod n) ^ (c - 1) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
    push_cast at this
    exact this
  have z2 : (2 : ZMod n) ^ (Nat.totient n) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
    push_cast at this
    exact this
  have zg : (2 : ZMod n) ^ Nat.gcd (c - 1) (Nat.totient n) = 1 := pow_gcd_eq_one.mpr ⟨z1, z2⟩
  set g := Nat.gcd (c - 1) (Nat.totient n) with hg
  have hgp : g ∣ p - 1 := by
    have hg1 : g ∣ p ^ (2 * k - 1) * (p - 1) := htot ▸ Nat.gcd_dvd_right _ _
    have hgc : Nat.Coprime g (p ^ (2 * k - 1)) :=
      Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hcop)
    exact hgc.dvd_of_dvd_mul_left hg1
  have hgm : g ∣ m - 1 := by
    have e1 : p ≡ 1 [MOD g] := ((Nat.modEq_iff_dvd' hp.one_le).mpr hgp).symm
    have e2 : c ≡ 1 [MOD g] := ((Nat.modEq_iff_dvd' hc1).mpr (Nat.gcd_dvd_left _ _)).symm
    have e3 : p ^ k * m ≡ 1 ^ k * m [MOD g] := (e1.pow k).mul_right m
    rw [one_pow, one_mul, ← hc] at e3
    exact (Nat.modEq_iff_dvd' hm).mp (e3.symm.trans e2).symm
  have back : ∀ e, g ∣ e → 2 ^ e ≡ 1 [MOD n] := by
    intro e he
    obtain ⟨t, ht⟩ := he
    have : (2 : ZMod n) ^ e = 1 := by rw [ht, pow_mul, zg, one_pow]
    have h' : ((2 ^ e : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by push_cast; exact this
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h'
  exact ⟨back _ hgp, back _ hgm⟩

/-- Every prime factor of a solution is a Wieferich prime. -/
theorem wief_prime_factor (c p : ℕ) (hc : 0 < c) (hp : p.Prime) (hpc : p ∣ c)
    (h : 2 ^ (c - 1) ≡ 1 [MOD c ^ 2]) : 2 ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  obtain ⟨m, hm⟩ := hpc
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; omega
    · exact h0
  have := (wief_cofactor c p 1 m hp le_rfl hm1 (by rw [hm, pow_one]) h).1
  simpa using this

/-- The order of 2 modulo p^2 divides c - 1. -/
theorem wief_orderOf_dvd (c p : ℕ) (hpc : p ∣ c)
    (h : 2 ^ (c - 1) ≡ 1 [MOD c ^ 2]) : orderOf (2 : ZMod (p ^ 2)) ∣ c - 1 := by
  apply orderOf_dvd_of_pow_eq_one
  have hd : p ^ 2 ∣ c ^ 2 := pow_dvd_pow_of_dvd hpc 2
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.of_dvd hd h)
  push_cast at this
  exact this

/-- A repeated prime factor p would need 2^(p-1) ≡ 1 (mod p^4). -/
theorem wief_sq_factor (c p : ℕ) (hc : 0 < c) (hp : p.Prime) (hpc : p ^ 2 ∣ c)
    (h : 2 ^ (c - 1) ≡ 1 [MOD c ^ 2]) : 2 ^ (p - 1) ≡ 1 [MOD p ^ 4] := by
  obtain ⟨m, hm⟩ := hpc
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; omega
    · exact h0
  exact (wief_cofactor c p 2 m hp (by norm_num) hm1 hm h).1

theorem not_modEq_1093_4 : ¬ 2 ^ 1092 ≡ 1 [MOD 1093 ^ 4] := by
  unfold Nat.ModEq; rw [← powMod_eq]; decide +kernel

theorem not_modEq_3511_4 : ¬ 2 ^ 3510 ≡ 1 [MOD 3511 ^ 4] := by
  unfold Nat.ModEq; rw [← powMod_eq]; decide +kernel

theorem not_modEq_3510_1093 : ¬ 2 ^ 3510 ≡ 1 [MOD 1093 ^ 2] := by
  unfold Nat.ModEq; rw [← powMod_eq]; decide +kernel

/-- 1093^2 divides no solution. -/
theorem wief_not_1093_sq (c : ℕ) (hc : 0 < c) (hd : 1093 ^ 2 ∣ c)
    (h : 2 ^ (c - 1) ≡ 1 [MOD c ^ 2]) : False :=
  by
    have hw := wief_sq_factor c 1093 hc (by norm_num) hd h
    rw [show (1093 : ℕ) - 1 = 1092 by norm_num] at hw
    exact not_modEq_1093_4 hw

/-- 3511^2 divides no solution. -/
theorem wief_not_3511_sq (c : ℕ) (hc : 0 < c) (hd : 3511 ^ 2 ∣ c)
    (h : 2 ^ (c - 1) ≡ 1 [MOD c ^ 2]) : False :=
  by
    have hw := wief_sq_factor c 3511 hc (by norm_num) hd h
    rw [show (3511 : ℕ) - 1 = 3510 by norm_num] at hw
    exact not_modEq_3511_4 hw

/-- No product of powers of the two known Wieferich primes with at least two prime factors
(counted with multiplicity) is a solution. -/
theorem wief_no_1093_3511 (a b : ℕ) (hab : 2 ≤ a + b) :
    ¬ 2 ^ (1093 ^ a * 3511 ^ b - 1) ≡ 1 [MOD (1093 ^ a * 3511 ^ b) ^ 2] := by
  intro h
  have hc : 0 < 1093 ^ a * 3511 ^ b := by positivity
  rcases Nat.lt_or_ge a 2 with ha | ha
  · rcases Nat.lt_or_ge b 2 with hb | hb
    · have ha1 : a = 1 := by omega
      have hb1 : b = 1 := by omega
      subst ha1 hb1
      have := (wief_cofactor _ 1093 1 3511 (by norm_num) le_rfl (by norm_num) (by norm_num) h).2
      rw [show (3511 : ℕ) - 1 = 3510 by norm_num, show 2 * 1 = 2 by norm_num] at this
      exact not_modEq_3510_1093 this
    · apply wief_not_3511_sq _ hc _ h
      exact Dvd.dvd.mul_left (pow_dvd_pow 3511 hb) _
  · apply wief_not_1093_sq _ hc _ h
    exact Dvd.dvd.mul_right (pow_dvd_pow 1093 ha) _

/-- If P^2 divides a product of distinct certified primes' powers, P occurs with exponent
at least 2. -/
theorem sq_dvd_factorsProd :
    ∀ (fs : List (ℕ × ℕ)), (∀ qk ∈ fs, qk.1.Prime) → (fs.map Prod.fst).Nodup →
      ∀ P : ℕ, P.Prime → P ^ 2 ∣ factorsProd fs → ∃ qk ∈ fs, qk.1 = P ∧ 2 ≤ qk.2
  | [], _, _, P, hP, h => by
    have h1 := Nat.le_of_dvd one_pos h
    have h2 := hP.two_le
    simp at h1
    nlinarith
  | qk :: rest, hfs, hnd, P, hP, h => by
    simp only [factorsProd] at h
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hq : qk.1.Prime := hfs qk (by simp)
    by_cases hqP : qk.1 = P
    · have hnr : ¬ P ∣ factorsProd rest := by
        intro hd
        obtain ⟨qk', hmem, he⟩ :=
          exists_mem_of_prime_dvd_factorsProd rest (fun x hx => hfs x (by simp [hx])) P hP hd
        apply hnd.1
        rw [hqP, ← he]
        exact List.mem_map_of_mem hmem
      have hcop : Nat.Coprime (P ^ 2) (factorsProd rest) :=
        Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hP).mpr hnr)
      have h2 : P ^ 2 ∣ P ^ qk.2 := by
        rw [← hqP] at h ⊢
        exact (hqP ▸ hcop).dvd_of_dvd_mul_right h
      exact ⟨qk, by simp, hqP, (Nat.pow_dvd_pow_iff_le_right hP.one_lt).mp h2⟩
    · have hnq : ¬ P ∣ qk.1 ^ qk.2 := by
        intro hd
        exact hqP ((Nat.prime_dvd_prime_iff_eq hP hq).mp (hP.dvd_of_dvd_pow hd)).symm
      have hcop : Nat.Coprime (P ^ 2) (qk.1 ^ qk.2) :=
        Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hP).mpr hnq)
      obtain ⟨qk', hmem, he, hk⟩ :=
        sq_dvd_factorsProd rest (fun x hx => hfs x (by simp [hx])) hnd.2 P hP
          (hcop.dvd_of_dvd_mul_left h)
      exact ⟨qk', by simp [hmem], he, hk⟩

def fs1092 : List (ℕ × ℕ) :=
  [(3, 2),
   (5, 1),
   (7, 2),
   (13, 2),
   (29, 1),
   (43, 1),
   (53, 1),
   (79, 1),
   (113, 1),
   (127, 1),
   (157, 1),
   (313, 1),
   (337, 1),
   (547, 1),
   (911, 1),
   (1093, 2),
   (1249, 1),
   (1429, 1),
   (1613, 1),
   (2731, 1),
   (3121, 1),
   (4733, 1),
   (5419, 1),
   (8191, 1),
   (14449, 1),
   (21841, 1),
   (121369, 1),
   (224771, 1),
   (503413, 1),
   (1210483, 1),
   (1948129, 1),
   (22366891, 1),
   (108749551, 1),
   (112901153, 1),
   (23140471537, 1),
   (25829691707, 1),
   (105310750819, 1),
   (467811806281, 1),
   (4093204977277417, 1),
   (8861085190774909, 1),
   (556338525912325157, 1),
   (86977595801949844993, 1),
   (275700717951546566946854497, 1),
   (292653113147157205779127526827, 1),
   (3194753987813988499397428643895659569, 1)]

def cert1092 : List PrattStep :=
  [⟨2, 1, []⟩,
   ⟨3, 2, [(2, 1)]⟩,
   ⟨5, 2, [(2, 2)]⟩,
   ⟨7, 3, [(2, 1), (3, 1)]⟩,
   ⟨13, 2, [(2, 2), (3, 1)]⟩,
   ⟨29, 2, [(2, 2), (7, 1)]⟩,
   ⟨43, 3, [(2, 1), (3, 1), (7, 1)]⟩,
   ⟨53, 2, [(2, 2), (13, 1)]⟩,
   ⟨79, 3, [(2, 1), (3, 1), (13, 1)]⟩,
   ⟨113, 3, [(2, 4), (7, 1)]⟩,
   ⟨127, 3, [(2, 1), (3, 2), (7, 1)]⟩,
   ⟨157, 5, [(2, 2), (3, 1), (13, 1)]⟩,
   ⟨313, 10, [(2, 3), (3, 1), (13, 1)]⟩,
   ⟨337, 10, [(2, 4), (3, 1), (7, 1)]⟩,
   ⟨547, 2, [(2, 1), (3, 1), (7, 1), (13, 1)]⟩,
   ⟨911, 17, [(2, 1), (5, 1), (7, 1), (13, 1)]⟩,
   ⟨1093, 5, [(2, 2), (3, 1), (7, 1), (13, 1)]⟩,
   ⟨1249, 7, [(2, 5), (3, 1), (13, 1)]⟩,
   ⟨17, 3, [(2, 4)]⟩,
   ⟨1429, 6, [(2, 2), (3, 1), (7, 1), (17, 1)]⟩,
   ⟨31, 3, [(2, 1), (3, 1), (5, 1)]⟩,
   ⟨1613, 3, [(2, 2), (13, 1), (31, 1)]⟩,
   ⟨2731, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1)]⟩,
   ⟨3121, 7, [(2, 4), (3, 1), (5, 1), (13, 1)]⟩,
   ⟨4733, 5, [(2, 2), (7, 1), (13, 2)]⟩,
   ⟨5419, 3, [(2, 1), (3, 2), (7, 1), (43, 1)]⟩,
   ⟨8191, 17, [(2, 1), (3, 2), (5, 1), (7, 1), (13, 1)]⟩,
   ⟨14449, 22, [(2, 4), (3, 1), (7, 1), (43, 1)]⟩,
   ⟨21841, 11, [(2, 4), (3, 1), (5, 1), (7, 1), (13, 1)]⟩,
   ⟨97, 5, [(2, 5), (3, 1)]⟩,
   ⟨389, 2, [(2, 2), (97, 1)]⟩,
   ⟨121369, 7, [(2, 3), (3, 1), (13, 1), (389, 1)]⟩,
   ⟨19, 2, [(2, 1), (3, 2)]⟩,
   ⟨224771, 6, [(2, 1), (5, 1), (7, 1), (13, 2), (19, 1)]⟩,
   ⟨11, 2, [(2, 1), (5, 1)]⟩,
   ⟨23, 5, [(2, 1), (11, 1)]⟩,
   ⟨461, 2, [(2, 2), (5, 1), (23, 1)]⟩,
   ⟨503413, 6, [(2, 2), (3, 1), (7, 1), (13, 1), (461, 1)]⟩,
   ⟨41, 6, [(2, 3), (5, 1)]⟩,
   ⟨739, 3, [(2, 1), (3, 2), (41, 1)]⟩,
   ⟨1210483, 5, [(2, 1), (3, 2), (7, 1), (13, 1), (739, 1)]⟩,
   ⟨37, 2, [(2, 2), (3, 2)]⟩,
   ⟨223, 3, [(2, 1), (3, 1), (37, 1)]⟩,
   ⟨1948129, 11, [(2, 5), (3, 1), (7, 1), (13, 1), (223, 1)]⟩,
   ⟨22366891, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (13, 1), (2731, 1)]⟩,
   ⟨257, 3, [(2, 8)]⟩,
   ⟨108749551, 6, [(2, 1), (3, 1), (5, 2), (7, 1), (13, 1), (31, 1), (257, 1)]⟩,
   ⟨137, 3, [(2, 3), (17, 1)]⟩,
   ⟨47, 5, [(2, 1), (23, 1)]⟩,
   ⟨283, 3, [(2, 1), (3, 1), (47, 1)]⟩,
   ⟨112901153, 3, [(2, 5), (7, 1), (13, 1), (137, 1), (283, 1)]⟩,
   ⟨109, 6, [(2, 2), (3, 3)]⟩,
   ⟨953, 3, [(2, 3), (7, 1), (17, 1)]⟩,
   ⟨23140471537, 43, [(2, 4), (3, 2), (7, 1), (13, 1), (17, 1), (109, 1), (953, 1)]⟩,
   ⟨727, 5, [(2, 1), (3, 1), (11, 2)]⟩,
   ⟨2909, 2, [(2, 2), (727, 1)]⟩,
   ⟨173, 2, [(2, 2), (43, 1)]⟩,
   ⟨48787, 2, [(2, 1), (3, 1), (47, 1), (173, 1)]⟩,
   ⟨25829691707, 5, [(2, 1), (7, 1), (13, 1), (2909, 1), (48787, 1)]⟩,
   ⟨1549, 2, [(2, 2), (3, 2), (43, 1)]⟩,
   ⟨3037, 2, [(2, 2), (3, 1), (11, 1), (23, 1)]⟩,
   ⟨105310750819, 7, [(2, 1), (3, 1), (7, 1), (13, 1), (41, 1), (1549, 1), (3037, 1)]⟩,
   ⟨71, 7, [(2, 1), (5, 1), (7, 1)]⟩,
   ⟨163, 2, [(2, 1), (3, 4)]⟩,
   ⟨653, 2, [(2, 2), (163, 1)]⟩,
   ⟨86197, 2, [(2, 2), (3, 1), (11, 1), (653, 1)]⟩,
   ⟨467811806281, 11, [(2, 3), (3, 1), (5, 1), (7, 2), (13, 1), (71, 1), (86197, 1)]⟩,
   ⟨107, 2, [(2, 1), (53, 1)]⟩,
   ⟨421, 2, [(2, 2), (3, 1), (5, 1), (7, 1)]⟩,
   ⟨61, 2, [(2, 2), (3, 1), (5, 1)]⟩,
   ⟨5003, 2, [(2, 1), (41, 1), (61, 1)]⟩,
   ⟨176926093, 2, [(2, 2), (3, 1), (7, 1), (421, 1), (5003, 1)]⟩,
   ⟨4093204977277417, 19, [(2, 3), (3, 3), (7, 1), (11, 1), (13, 1), (107, 1), (176926093, 1)]⟩,
   ⟨1543, 5, [(2, 1), (3, 1), (257, 1)]⟩,
   ⟨2953, 13, [(2, 3), (3, 2), (41, 1)]⟩,
   ⟨593627, 2, [(2, 1), (11, 3), (223, 1)]⟩,
   ⟨8861085190774909, 6, [(2, 2), (3, 2), (7, 1), (13, 1), (1543, 1), (2953, 1), (593627, 1)]⟩,
   ⟨109717, 5, [(2, 2), (3, 1), (41, 1), (223, 1)]⟩,
   ⟨658303, 6, [(2, 1), (3, 1), (109717, 1)]⟩,
   ⟨2852249, 3, [(2, 3), (7, 1), (31, 2), (53, 1)]⟩,
   ⟨5704499, 2, [(2, 1), (2852249, 1)]⟩,
   ⟨556338525912325157, 3, [(2, 2), (7, 1), (11, 1), (13, 1), (37, 1), (658303, 1), (5704499, 1)]⟩,
   ⟨4889, 3, [(2, 3), (13, 1), (47, 1)]⟩,
   ⟨2287, 19, [(2, 1), (3, 2), (127, 1)]⟩,
   ⟨68611, 2, [(2, 1), (3, 1), (5, 1), (2287, 1)]⟩,
   ⟨347, 2, [(2, 1), (173, 1)]⟩,
   ⟨168643, 2, [(2, 1), (3, 5), (347, 1)]⟩,
   ⟨86977595801949844993, 5, [(2, 9), (3, 1), (7, 1), (11, 1), (13, 1), (4889, 1), (68611, 1), (168643, 1)]⟩,
   ⟨2557, 2, [(2, 2), (3, 2), (71, 1)]⟩,
   ⟨46027, 2, [(2, 1), (3, 2), (2557, 1)]⟩,
   ⟨131, 2, [(2, 1), (5, 1), (13, 1)]⟩,
   ⟨263, 5, [(2, 1), (131, 1)]⟩,
   ⟨373, 2, [(2, 2), (3, 1), (31, 1)]⟩,
   ⟨59659, 3, [(2, 1), (3, 1), (61, 1), (163, 1)]⟩,
   ⟨456494082799, 6, [(2, 1), (3, 1), (13, 1), (263, 1), (373, 1), (59659, 1)]⟩,
   ⟨36087683221592147, 2, [(2, 1), (29, 2), (47, 1), (456494082799, 1)]⟩,
   ⟨275700717951546566946854497, 30, [(2, 5), (3, 1), (7, 1), (13, 1), (19, 1), (46027, 1), (36087683221592147, 1)]⟩,
   ⟨181, 2, [(2, 2), (3, 2), (5, 1)]⟩,
   ⟨1087, 3, [(2, 1), (3, 1), (181, 1)]⟩,
   ⟨5431, 3, [(2, 1), (3, 1), (5, 1), (181, 1)]⟩,
   ⟨32587, 2, [(2, 1), (3, 1), (5431, 1)]⟩,
   ⟨130241, 3, [(2, 6), (5, 1), (11, 1), (37, 1)]⟩,
   ⟨260483, 2, [(2, 1), (130241, 1)]⟩,
   ⟨16976719043, 2, [(2, 1), (32587, 1), (260483, 1)]⟩,
   ⟨5651, 2, [(2, 1), (5, 2), (113, 1)]⟩,
   ⟨9283, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (17, 1)]⟩,
   ⟨13183, 3, [(2, 1), (3, 1), (13, 3)]⟩,
   ⟨9681796398947, 2, [(2, 1), (7, 1), (5651, 1), (9283, 1), (13183, 1)]⟩,
   ⟨292653113147157205779127526827, 7, [(2, 1), (3, 2), (7, 1), (13, 1), (1087, 1), (16976719043, 1), (9681796398947, 1)]⟩,
   ⟨37447, 3, [(2, 1), (3, 1), (79, 2)]⟩,
   ⟨224683, 3, [(2, 1), (3, 1), (37447, 1)]⟩,
   ⟨239, 7, [(2, 1), (7, 1), (17, 1)]⟩,
   ⟨479, 13, [(2, 1), (239, 1)]⟩,
   ⟨3833, 3, [(2, 3), (479, 1)]⟩,
   ⟨1195897, 5, [(2, 3), (3, 1), (13, 1), (3833, 1)]⟩,
   ⟨57403057, 5, [(2, 4), (3, 1), (1195897, 1)]⟩,
   ⟨1321, 13, [(2, 3), (3, 1), (5, 1), (11, 1)]⟩,
   ⟨39631, 3, [(2, 1), (3, 1), (5, 1), (1321, 1)]⟩,
   ⟨281, 3, [(2, 3), (5, 1), (7, 1)]⟩,
   ⟨563, 2, [(2, 1), (281, 1)]⟩,
   ⟨521, 3, [(2, 3), (5, 1), (13, 1)]⟩,
   ⟨18757, 2, [(2, 2), (3, 2), (521, 1)]⟩,
   ⟨21120383, 5, [(2, 1), (563, 1), (18757, 1)]⟩,
   ⟨1819685607715103, 5, [(2, 1), (1087, 1), (39631, 1), (21120383, 1)]⟩,
   ⟨61419843797108821994684149, 2, [(2, 2), (3, 1), (7, 2), (57403057, 1), (1819685607715103, 1)]⟩,
   ⟨3194753987813988499397428643895659569, 23, [(2, 4), (3, 1), (7, 1), (13, 1), (53, 1), (224683, 1), (61419843797108821994684149, 1)]⟩]

/-- 2^1092 - 1 is the product of the listed prime powers. -/
theorem factorsProd_1092 : factorsProd fs1092 = 2 ^ 1092 - 1 := by decide +kernel

theorem primes_1092 : ∀ qk ∈ fs1092, qk.1.Prime := by
  have h := primes_of_prattCertifiesAll (fs1092.map Prod.fst) cert1092 (by decide +kernel)
  intro qk hqk
  exact h _ (List.mem_map_of_mem hqk)

theorem nodup_1092 : (fs1092.map Prod.fst).Nodup := by decide +kernel

/-- The primes whose square divides 2^1092 - 1 are 3, 7, 13 and 1093. -/
theorem sq_dvd_two_pow_1092 (P : ℕ) (hP : P.Prime) (h : P ^ 2 ∣ 2 ^ 1092 - 1) :
    P = 3 ∨ P = 7 ∨ P = 13 ∨ P = 1093 := by
  rw [← factorsProd_1092] at h
  obtain ⟨qk, hmem, he, hk⟩ := sq_dvd_factorsProd fs1092 primes_1092 nodup_1092 P hP h
  have hall : ∀ qk ∈ fs1092, 2 ≤ qk.2 → qk.1 = 3 ∨ qk.1 = 7 ∨ qk.1 = 13 ∨ qk.1 = 1093 := by
    decide +kernel
  rw [← he]
  exact hall qk hmem hk

/-- No c = 1093^a * P^k (a, k ≥ 1, P ≠ 1093 prime) is a solution: a ≥ 2 is excluded by
`wief_not_1093_sq`; for a = 1 the cofactor lemma gives P^2 ∣ 2^1092 - 1, so P is 3, 7 or 13,
none of which is a Wieferich prime. -/
theorem wief_no_1093_prime_power (a k P : ℕ) (hP : P.Prime) (hP1093 : P ≠ 1093)
    (ha : 1 ≤ a) (hk : 1 ≤ k) :
    ¬ 2 ^ (1093 ^ a * P ^ k - 1) ≡ 1 [MOD (1093 ^ a * P ^ k) ^ 2] := by
  intro h
  have hc : 0 < 1093 ^ a * P ^ k := by have := hP.pos; positivity
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · have ha1 : a = 1 := by omega
    subst ha1
    have hw := wief_cofactor _ P k 1093 hP hk (by norm_num) (by ring) h
    rw [show (1093 : ℕ) - 1 = 1092 by norm_num] at hw
    have hsq : P ^ 2 ∣ P ^ (2 * k) := pow_dvd_pow P (by omega)
    have key : ∀ E : ℕ, 0 < E → E ≡ 1 [MOD P ^ (2 * k)] → P ^ (2 * k) ∣ E - 1 :=
      fun E hE he => (Nat.modEq_iff_dvd' hE).mp he.symm
    have h1 : P ^ 2 ∣ 2 ^ 1092 - 1 := hsq.trans (key (2 ^ 1092) (by positivity) hw.2)
    have h2 : 2 ^ (P - 1) ≡ 1 [MOD P ^ 2] := Nat.ModEq.of_dvd hsq hw.1
    rcases sq_dvd_two_pow_1092 P hP h1 with rfl | rfl | rfl | rfl
    · exact absurd h2 (by decide)
    · exact absurd h2 (by decide)
    · exact absurd h2 (by decide)
    · exact hP1093 rfl
  · apply wief_not_1093_sq _ hc _ h
    exact Dvd.dvd.mul_right (pow_dvd_pow 1093 ha2) _
