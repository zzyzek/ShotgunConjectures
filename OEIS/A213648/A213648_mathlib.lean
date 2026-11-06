/-
OEIS A213648 (partial): Fibonacci entry-point facts used in the README.

Main theorems.
* `EP_prime`: if n ≥ 2, n ∣ F(n+1) and n ∤ F(m) for 1 ≤ m ≤ n (entry point n + 1), then n is prime.
* `kam`: for a prime p, p ∣ F(p-1) ∨ p ∣ F(p) ∨ p ∣ F(p+1).
  (Over ZMod p, with A = [[1,1],[1,0]]: A + 1 = A^2 and (A + 1)^p = A^p + 1, so
  (A^p)^2 = A^p + 1; compare entries of A^p = [[F(p+1), F(p)], [F(p), F(p-1)]].)
-/
import Mathlib

open Nat

namespace A213648

def Am (p : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod p) := !![1, 1; 1, 0]

theorem Am_pow (p n : ℕ) : Am p ^ (n + 1) =
    !![((fib (n + 2) : ℕ) : ZMod p), (fib (n + 1) : ZMod p); (fib (n + 1) : ZMod p), (fib n : ZMod p)] := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [Am]
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Am, Matrix.mul_apply, Fin.sum_univ_two, fib_add_two] <;> ring

theorem kam (p : ℕ) [hp : Fact p.Prime] : p ∣ fib (p - 1) ∨ p ∣ fib p ∨ p ∣ fib (p + 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_lt.le).symm⟩
  have hsq : Am (q + 1) ^ 2 = Am (q + 1) + 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Am, sq, Matrix.mul_apply, Fin.sum_univ_two]
  have hfr : (Am (q + 1) + 1) ^ (q + 1) = Am (q + 1) ^ (q + 1) + 1 := by
    rw [add_pow_char_of_commute (p := q + 1) (Commute.one_right _), one_pow]
  rw [← hsq, ← pow_mul, show 2 * (q + 1) = (q + 1) + (q + 1) by ring, pow_add, Am_pow] at hfr
  set a : ZMod (q + 1) := (fib (q + 1) : ZMod (q + 1))
  set b : ZMod (q + 1) := (fib q : ZMod (q + 1))
  have h2 : ((fib (q + 2) : ℕ) : ZMod (q + 1)) = a + b := by
    simp only [a, b]; rw [fib_add_two]; push_cast; ring
  rw [h2] at hfr
  have e01 := congrArg (fun M => M 0 1) hfr
  have e11 := congrArg (fun M => M 1 1) hfr
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e11
  -- e01 : (a + b) * a + a * b = a,  e11 : a * a + b * b = b + 1
  have hcast : ∀ k, ((fib k : ℕ) : ZMod (q + 1)) = 0 ↔ q + 1 ∣ fib k := fun k =>
    ZMod.natCast_eq_zero_iff _ _
  have key : a * (a + 2 * b - 1) = 0 := by linear_combination e01
  rcases mul_eq_zero.1 key with ha | ha
  · right; left; exact (hcast _).1 ha
  · have hab : a = 1 - 2 * b := by linear_combination ha
    have h5 : (5 : ZMod (q + 1)) * (b * (b - 1)) = 0 := by
      rw [hab] at e11; linear_combination e11
    rcases mul_eq_zero.1 h5 with h | h
    · -- p ∣ 5, so p = 5 and 5 ∣ F(5)
      have h5' : q + 1 ∣ 5 := by
        have : ((5 : ℕ) : ZMod (q + 1)) = 0 := by exact_mod_cast h
        exact (ZMod.natCast_eq_zero_iff _ _).1 this
      have hq : q + 1 = 5 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 h5' with h | h
        · exact absurd h hp.out.one_lt.ne'
        · exact h
      right; left; rw [hq]; decide
    · rcases mul_eq_zero.1 h with h | h
      · left; simpa using (hcast q).1 h
      · right; right
        have hb : b = 1 := by linear_combination h
        apply (hcast (q + 1 + 1)).1
        rw [show q + 1 + 1 = q + 2 by ring, h2, hab, hb]; ring


theorem dvd_fib_gcd {d a b : ℕ} (ha : d ∣ fib a) (hb : d ∣ fib b) : d ∣ fib (Nat.gcd a b) := by
  rw [Nat.fib_gcd]; exact Nat.dvd_gcd ha hb

theorem lift1 (p a : ℕ) (ha : (fib a : ZMod p) = 0) :
    ∀ t, (fib (a * t + 1) : ZMod p) = (fib (a + 1) : ZMod p) ^ t := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show a * (t + 1) + 1 = a * t + a + 1 by ring, fib_add]
    push_cast
    rw [ha, ih]; ring

theorem lift2 (p a : ℕ) (ha1 : 1 ≤ a) (ha : (fib a : ZMod p) = 0) :
    ∀ t, ∃ u, fib (a * (t + 1)) = fib a * u ∧
      (u : ZMod p) = ((t : ZMod p) + 1) * (fib (a + 1) : ZMod p) ^ t := by
  intro t
  induction t with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ t ih =>
    obtain ⟨u, hu, hu'⟩ := ih
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    refine ⟨u * fib a' + fib ((a' + 1) * (t + 1) + 1), ?_, ?_⟩
    · rw [show (a' + 1) * (t + 1 + 1) = (a' + 1) * (t + 1) + a' + 1 by ring, fib_add, hu]
      ring
    · have hc : (fib a' : ZMod p) = (fib (a' + 1 + 1) : ZMod p) := by
        rw [fib_add_two]; push_cast; rw [ha]; ring
      push_cast
      rw [hu', hc, lift1 p (a' + 1) ha (t + 1)]
      ring

/-- Lifting: if p ∣ F(a), p ∤ t and p^e ∣ F(a t) then p^e ∣ F(a). -/
theorem lift (p a t e : ℕ) (hp : p.Prime) (ha1 : 1 ≤ a) (hpa : p ∣ fib a) (ht1 : 1 ≤ t)
    (hpt : ¬ p ∣ t) (he : p ^ e ∣ fib (a * t)) : p ^ e ∣ fib a := by
  have hF : Fact p.Prime := ⟨hp⟩
  have ha : (fib a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpa
  obtain ⟨u, hu, hu'⟩ := lift2 p a ha1 ha (t - 1)
  rw [show t - 1 + 1 = t by omega] at hu
  have hc : (fib (a + 1) : ZMod p) ≠ 0 := by
    intro h
    have h1 : p ∣ fib (a + 1) := (ZMod.natCast_eq_zero_iff _ _).1 h
    have h2 := Nat.dvd_gcd hpa h1
    rw [(Nat.fib_coprime_fib_succ a).gcd_eq_one] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have htz : ((t - 1 : ℕ) : ZMod p) + 1 ≠ 0 := by
    intro h
    have : ((t : ℕ) : ZMod p) = 0 := by
      rw [show t = (t - 1) + 1 by omega]; push_cast; exact h
    exact hpt ((ZMod.natCast_eq_zero_iff _ _).1 this)
  have hu0 : ¬ p ∣ u := by
    intro h
    have h0 : (u : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    rw [hu'] at h0
    exact (mul_ne_zero htz (pow_ne_zero _ hc)) h0
  have hcop : Nat.Coprime (p ^ e) u :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hu0)
  rw [hu] at he
  exact hcop.dvd_of_dvd_mul_right he

/-- The entry-point hypothesis z(n) = n + 1, stated without defining z. -/
def EP (n : ℕ) : Prop := n ∣ fib (n + 1) ∧ ∀ m, 1 ≤ m → m ≤ n → ¬ n ∣ fib m

theorem EP_dvd {n : ℕ} (h : EP n) {d : ℕ} (hd : 1 ≤ d) (hnd : n ∣ fib d) : n + 1 ∣ d := by
  have hg := dvd_fib_gcd h.1 hnd
  have g1 : 1 ≤ Nat.gcd (n + 1) d := Nat.gcd_pos_of_pos_right _ hd
  have g2 : Nat.gcd (n + 1) d ≤ n + 1 := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  have : Nat.gcd (n + 1) d = n + 1 := by
    by_contra hne
    exact h.2 _ g1 (by omega) hg
  rw [← this]; exact Nat.gcd_dvd_right _ _

/-- Per prime: p^e ∥-part of n divides F(g) for some g ∣ n+1 dividing p - 1 or p + 1. -/
theorem per_prime {n : ℕ} (h : EP n) (p e : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hpe : p ^ e ∣ n) :
    ∃ g, g ∣ n + 1 ∧ 1 ≤ g ∧ p ^ e ∣ fib g ∧ (g ∣ p - 1 ∨ g ∣ p + 1) := by
  have hF : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  have hpq : ¬ p ∣ n + 1 := by
    intro h'; have := (Nat.dvd_add_right hpn).1 h'; exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hpF : p ∣ fib (n + 1) := dvd_trans hpn h.1
  -- d with p ∣ F(d), d = p ± 1
  have key : ∀ d, 1 ≤ d → p ∣ fib d → (d = p - 1 ∨ d = p + 1) →
      ∃ g, g ∣ n + 1 ∧ 1 ≤ g ∧ p ^ e ∣ fib g ∧ (g ∣ p - 1 ∨ g ∣ p + 1) := by
    intro d hd1 hpd hdd
    set g := Nat.gcd (n + 1) d
    have g1 : 1 ≤ g := Nat.gcd_pos_of_pos_left _ (by omega)
    have hpg : p ∣ fib g := dvd_fib_gcd hpF hpd
    obtain ⟨t, ht⟩ := Nat.gcd_dvd_left (n + 1) d
    have ht1 : 1 ≤ t := by rcases Nat.eq_zero_or_pos t with h0 | h0 <;> [simp [h0] at ht; omega]
    have hpt : ¬ p ∣ t := fun hd => hpq (by rw [ht]; exact Dvd.dvd.mul_left hd _)
    have hpe' : p ^ e ∣ fib (g * t) := by rw [← ht]; exact dvd_trans hpe h.1
    refine ⟨g, Nat.gcd_dvd_left _ _, g1, lift p g t e hp g1 hpg ht1 hpt hpe', ?_⟩
    rcases hdd with rfl | rfl
    · left; exact Nat.gcd_dvd_right _ _
    · right; exact Nat.gcd_dvd_right _ _
  rcases kam p with h1 | h1 | h1
  · exact key _ (by omega) h1 (Or.inl rfl)
  · exfalso
    have hg1 : Nat.gcd (n + 1) p = 1 :=
      Nat.Coprime.gcd_eq_one ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq))
    have := dvd_fib_gcd hpF h1
    rw [hg1] at this
    simp at this; exact hp.one_lt.ne' this
  · exact key _ (by omega) h1 (Or.inr rfl)

/-- Prime powers with exponent ≥ 2 never have entry point n + 1. -/
theorem not_EP_prime_pow (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e) : ¬ EP (p ^ e) := by
  intro h
  have hp2 := hp.two_le
  obtain ⟨g, _, g1, hg, hgd⟩ := per_prime h p e hp (dvd_pow_self p (by omega)) dvd_rfl
  have hgle : g ≤ p + 1 := by
    rcases hgd with h' | h'
    · have := Nat.le_of_dvd (by omega) h'; omega
    · exact Nat.le_of_dvd (by omega) h'
  have hpe : p + 1 ≤ p ^ e := by
    calc p + 1 ≤ p * p := by nlinarith
      _ = p ^ 2 := by ring
      _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
  exact h.2 g g1 (by omega) hg

/-- Combining two coprime parts with an lcm of their entry indices. -/
theorem comb {n A B GA GB : ℕ} (hAB : Nat.Coprime A B) (hA : A ∣ fib GA) (hB : B ∣ fib GB)
    (hGA : GA ∣ n + 1) (hGB : GB ∣ n + 1) :
    Nat.lcm GA GB ∣ n + 1 ∧ A * B ∣ fib (Nat.lcm GA GB) := by
  refine ⟨Nat.lcm_dvd hGA hGB, hAB.mul_dvd_of_dvd_of_dvd ?_ ?_⟩
  · exact dvd_trans hA (Nat.fib_dvd _ _ (Nat.dvd_lcm_left _ _))
  · exact dvd_trans hB (Nat.fib_dvd _ _ (Nat.dvd_lcm_right _ _))

/-- The size bound for an lcm of two indices. -/
theorem ineq {a b GA GB : ℕ} (hA : 3 * GA ≤ 4 * a) (hB : 3 * GB ≤ 4 * b)
    (hAo : Odd GA → 3 * GA ≤ 2 * a) (hBo : Odd GB → 3 * GB ≤ 2 * b) (hGA : 1 ≤ GA) :
    9 * Nat.lcm GA GB ≤ 8 * (a * b) ∧ (Odd (Nat.lcm GA GB) → 3 * Nat.lcm GA GB ≤ 2 * (a * b)) := by
  have hgl := Nat.gcd_mul_lcm GA GB
  have hg1 : 1 ≤ Nat.gcd GA GB := Nat.gcd_pos_of_pos_left _ hGA
  have hL : Nat.lcm GA GB ≤ GA * GB := by nlinarith
  constructor
  · rcases Nat.even_or_odd GA with ⟨x, hx⟩ | hoA
    · rcases Nat.even_or_odd GB with ⟨y, hy⟩ | hoB
      · have h2 : 2 ∣ Nat.gcd GA GB := Nat.dvd_gcd ⟨x, by omega⟩ ⟨y, by omega⟩
        have hg2 : 2 ≤ Nat.gcd GA GB := Nat.le_of_dvd (by omega) h2
        have : 2 * Nat.lcm GA GB ≤ GA * GB := by nlinarith
        have := Nat.mul_le_mul hA hB
        nlinarith
      · have := Nat.mul_le_mul hA (hBo hoB); nlinarith
    · have := Nat.mul_le_mul (hAo hoA) hB; nlinarith
  · intro hoL
    have hoA : Odd GA := hoL.of_dvd_nat (Nat.dvd_lcm_left _ _)
    have hoB : Odd GB := hoL.of_dvd_nat (Nat.dvd_lcm_right _ _)
    have := Nat.mul_le_mul (hAo hoA) (hBo hoB)
    nlinarith

/-- Odd divisors m > 1 of n get an index G ∣ n+1 with m ∣ F(G) and 3G ≤ 4m (3G ≤ 2m if G is odd). -/
theorem claim {n : ℕ} (h : EP n) : ∀ m, m ∣ n → Odd m → 1 < m →
    ∃ G, G ∣ n + 1 ∧ 1 ≤ G ∧ m ∣ fib G ∧ 3 * G ≤ 4 * m ∧ (Odd G → 3 * G ≤ 2 * m) := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => intro _ h0; exact absurd h0 (by decide)
  | one => intro _ _ h1; omega
  | prime_pow p k hp hk =>
    intro hmn hodd _
    have hpk : p ∣ p ^ k := dvd_pow_self p (by omega)
    have hpo : Odd p := hodd.of_dvd_nat hpk
    have hp3 : 3 ≤ p := by
      rcases hpo with ⟨t, ht⟩; have := hp.two_le; omega
    have hle : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    obtain ⟨g, hg1, hg2, hg3, hg4⟩ := per_prime h p k hp (dvd_trans hpk hmn) hmn
    have hgx : ∃ x, g ∣ x ∧ x ≤ p + 1 ∧ 2 ∣ x ∧ 1 ≤ x := by
      rcases hpo with ⟨t, ht⟩
      rcases hg4 with h' | h'
      · exact ⟨p - 1, h', by omega, ⟨t, by omega⟩, by omega⟩
      · exact ⟨p + 1, h', le_rfl, ⟨t + 1, by omega⟩, by omega⟩
    obtain ⟨x, hgx, hx1, hx2, hx3⟩ := hgx
    have hgle : g ≤ x := Nat.le_of_dvd (by omega) hgx
    refine ⟨g, hg1, hg2, hg3, by omega, fun hgo => ?_⟩
    have hcop : Nat.Coprime 2 g := (Nat.coprime_two_left).2 hgo
    have h2g : 2 * g ∣ x := hcop.mul_dvd_of_dvd_of_dvd hx2 hgx
    have := Nat.le_of_dvd (by omega) h2g
    omega
  | coprime a b ha hb hab iha ihb =>
    intro hmn hodd _
    have hao : Odd a := (Nat.odd_mul.1 hodd).1
    have hbo : Odd b := (Nat.odd_mul.1 hodd).2
    obtain ⟨GA, hA1, hA2, hA3, hA4, hA5⟩ := iha (dvd_trans (dvd_mul_right a b) hmn) hao ha
    obtain ⟨GB, hB1, hB2, hB3, hB4, hB5⟩ := ihb (dvd_trans (dvd_mul_left b a) hmn) hbo hb
    obtain ⟨hL1, hL2⟩ := comb (n := n) hab hA3 hB3 hA1 hB1
    obtain ⟨i1, i2⟩ := ineq hA4 hB4 hA5 hB5 hA2
    exact ⟨Nat.lcm GA GB, hL1, Nat.lcm_pos hA2 hB2, hL2, by omega, fun ho => by have := i2 ho; omega⟩

/-- The step used in the README: if the Fibonacci entry point of n ≥ 2 is n + 1, then n is prime. -/
theorem EP_prime (n : ℕ) (hn : 2 ≤ n) (h : EP n) : n.Prime := by
  by_contra hnp
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  set e := n.factorization p with hedef
  have hnm : p ^ e * (n / p ^ e) = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop : Nat.Coprime p (n / p ^ e) := Nat.coprime_ordCompl hp (by omega)
  generalize n / p ^ e = m at hnm hcop
  have he1 : 1 ≤ e := hp.factorization_pos_of_dvd (by omega) hpn
  have hm0 : m ≠ 0 := by intro h0; rw [h0, mul_zero] at hnm; omega
  by_cases hm1 : m = 1
  · rw [hm1, mul_one] at hnm
    have he2 : 2 ≤ e := by
      by_contra hc
      have : e = 1 := by omega
      rw [this, pow_one] at hnm
      exact hnp (hnm ▸ hp)
    exact not_EP_prime_pow p e hp he2 (hnm ▸ h)
  · have hm2 : 2 ≤ m := by omega
    by_cases h2n : 2 ∣ n
    · have hp2 : p = 2 := (Nat.minFac_eq_two_iff n).2 h2n
      by_cases he2 : 2 ≤ e
      · exfalso
        have h4 : 2 ^ 2 ∣ n := by
          rw [← hnm, hp2]; exact dvd_trans (pow_dvd_pow 2 he2) (dvd_mul_right _ _)
        obtain ⟨g, _, g1, hg, hgd⟩ := per_prime h 2 2 Nat.prime_two (dvd_trans (by norm_num) h4) h4
        have : g = 1 ∨ g = 3 := by
          rcases hgd with h' | h'
          · left; exact Nat.dvd_one.1 h'
          · exact (Nat.dvd_prime (by norm_num)).1 h'
        rcases this with rfl | rfl
        · revert hg; decide
        · revert hg; decide
      · have he : e = 1 := by omega
        rw [he, hp2, pow_one] at hnm
        have hmo : Odd m := by
          rw [hp2] at hcop; exact (Nat.coprime_two_left).1 hcop
        obtain ⟨Gm, hm1', hm2', hm3', _, hm5'⟩ := claim h m ⟨2, by omega⟩ hmo (by omega)
        have hGo : Odd Gm := (show Odd (n + 1) from ⟨m, by omega⟩).of_dvd_nat hm1'
        have hG3 := hm5' hGo
        obtain ⟨g, hg1, g1, hg, hgd⟩ := per_prime h 2 1 Nat.prime_two h2n (by simpa using h2n)
        have hg3 : g = 3 := by
          rcases hgd with h' | h'
          · have : g = 1 := Nat.dvd_one.1 h'
            rw [this] at hg; exact absurd hg (by decide)
          · rcases (Nat.dvd_prime (by norm_num)).1 h' with h'' | h''
            · rw [h''] at hg; exact absurd hg (by decide)
            · exact h''
        rw [hg3] at hg hg1
        have hc2 : Nat.Coprime 2 m := by rw [hp2] at hcop; exact hcop
        obtain ⟨_, hL2⟩ := comb (n := n) hc2 (by simpa using hg) hm3' hg1 hm1'
        have hgl := Nat.gcd_mul_lcm 3 Gm
        have hg1' : 1 ≤ Nat.gcd 3 Gm := Nat.gcd_pos_of_pos_left _ (by norm_num)
        have hLle : Nat.lcm 3 Gm ≤ 3 * Gm := by nlinarith
        exact h.2 (Nat.lcm 3 Gm) (Nat.lcm_pos (by norm_num) hm2') (by omega) (by rw [← hnm]; exact hL2)
    · have hAo : Odd (p ^ e) := (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h2n)).of_dvd_nat ⟨m, hnm.symm⟩
      have hmo : Odd m := (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h2n)).of_dvd_nat ⟨p ^ e, by rw [← hnm, mul_comm]⟩
      have hA1 : 1 < p ^ e := Nat.one_lt_pow (by omega) hp.one_lt
      obtain ⟨GA, a1, a2, a3, a4, a5⟩ := claim h (p ^ e) ⟨m, hnm.symm⟩ hAo hA1
      obtain ⟨GB, b1, b2, b3, b4, b5⟩ := claim h m ⟨p ^ e, by rw [← hnm, mul_comm]⟩ hmo (by omega)
      obtain ⟨_, hL2⟩ := comb (n := n) (hcop.pow_left e) a3 b3 a1 b1
      obtain ⟨i1, _⟩ := ineq a4 b4 a5 b5 a2
      rw [hnm] at i1 hL2
      exact h.2 (Nat.lcm GA GB) (Nat.lcm_pos a2 b2) (by omega) hL2
