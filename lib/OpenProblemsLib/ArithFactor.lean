import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient

/-!
# σ, d and unitary divisors of a number given by its factorization

A factor list `f : List (ℕ × ℕ)` stands for `val f = ∏ p ^ e`. `FactOK f`: the bases are
primes (checked by trial division, `primeTD`) and pairwise distinct.

* `sigma_val`: `FactOK f → sigma 1 (val f) = sigF f` (product of `1 + p + … + p^e`);
* `card_divisors_val`: `FactOK f → #(val f).divisors = ndF f` (product of `e + 1`);
* `totient_val`: `FactOK f → (∀ pe ∈ f, 0 < pe.2) → φ (val f) = phiF f`;
* `unitary_val`: every unitary divisor `d` of `val f` (`d ∣ n`, `gcd(d, n/d) = 1`) is
  `val s` for a sublist `s` of `f`.

All three are by induction on `f` with multiplicativity of `σ k`
(`ArithmeticFunction.isMultiplicative_sigma`); the `Bool` functions evaluate in the kernel.
-/

namespace OpenProblemsLib.ArithFactor

open ArithmeticFunction

abbrev PF := List (ℕ × ℕ)

def val : PF → ℕ
  | [] => 1
  | pe :: r => pe.1 ^ pe.2 * val r

/-- `1 + p + … + p^e`. -/
def gsum (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | e + 1 => gsum p e + p ^ (e + 1)

def sigF : PF → ℕ
  | [] => 1
  | pe :: r => gsum pe.1 pe.2 * sigF r

def ndF : PF → ℕ
  | [] => 1
  | pe :: r => (pe.2 + 1) * ndF r

/-- Euler's totient from the factorization (exponents ≥ 1). -/
def phiF : PF → ℕ
  | [] => 1
  | pe :: r => pe.1 ^ (pe.2 - 1) * (pe.1 - 1) * phiF r

/-- Trial division by m, m+1, … while m² ≤ p (fuel f). -/
def tdLoop (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, m => decide (p < m * m) || (p % m != 0 && tdLoop p f (m + 1))

theorem tdLoop_spec (p : ℕ) : ∀ f m, tdLoop p f m = true → ∀ d, m ≤ d → d * d ≤ p → ¬ d ∣ p
  | 0, _, h, _, _, _ => by simp [tdLoop] at h
  | f + 1, m, h, d, hmd, hdd => by
    simp only [tdLoop, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne,
      ne_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · have : m * m ≤ d * d := Nat.mul_le_mul hmd hmd
      omega
    · rcases Nat.eq_or_lt_of_le hmd with he | hlt
      · subst he; exact fun hd => h1 (Nat.mod_eq_zero_of_dvd hd)
      · exact tdLoop_spec p f (m + 1) h2 d hlt hdd

/-- Trial-division primality up to √p. -/
def primeTD (p : ℕ) : Bool := 2 ≤ p && tdLoop p p 2

theorem prime_of_primeTD (p : ℕ) (h : primeTD p = true) : p.Prime := by
  simp only [primeTD, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [Nat.prime_def_le_sqrt]
  exact ⟨h.1, fun m hm hms => tdLoop_spec p p 2 h.2 m hm (Nat.le_sqrt.mp hms)⟩

def factCheck (f : PF) : Bool := (f.map Prod.fst).Nodup && f.all (fun pe => primeTD pe.1)

def FactOK (f : PF) : Prop := (f.map Prod.fst).Nodup ∧ ∀ pe ∈ f, pe.1.Prime

theorem factOK_of_check (f : PF) (h : factCheck f = true) : FactOK f := by
  simp only [factCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1, fun pe hpe => prime_of_primeTD _ (h.2 pe hpe)⟩

theorem FactOK.tail {pe : ℕ × ℕ} {r : PF} (h : FactOK (pe :: r)) : FactOK r :=
  ⟨(List.nodup_cons.mp h.1).2, fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩

theorem FactOK.sublist {f s : PF} (h : FactOK f) (hs : s.Sublist f) : FactOK s :=
  ⟨(hs.map Prod.fst).nodup h.1, fun q hq => h.2 q (hs.subset hq)⟩

theorem val_pos : ∀ f : PF, FactOK f → 0 < val f
  | [], _ => by simp [val]
  | pe :: r, h => by
    simp only [val]
    exact Nat.mul_pos (pow_pos (h.2 pe List.mem_cons_self).pos _) (val_pos r h.tail)

theorem coprime_head (pe : ℕ × ℕ) (r : PF) (h : FactOK (pe :: r)) :
    Nat.Coprime (pe.1 ^ pe.2) (val r) := by
  have hp := h.2 pe List.mem_cons_self
  have hn : pe.1 ∉ r.map Prod.fst := (List.nodup_cons.mp h.1).1
  have hr := h.tail
  clear h
  induction r with
  | nil => simp [val]
  | cons qe r ih =>
    simp only [val]
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.pow
      rw [Nat.coprime_primes hp (hr.2 qe List.mem_cons_self)]
      intro heq; apply hn; rw [heq]; exact List.mem_map_of_mem List.mem_cons_self
    · exact ih (fun hm => hn (List.mem_cons_of_mem _ hm)) hr.tail

theorem gsum_eq (p : ℕ) : ∀ e, gsum p e = ∑ k ∈ Finset.range (e + 1), p ^ k
  | 0 => by simp [gsum]
  | e + 1 => by rw [gsum, gsum_eq p e, Finset.sum_range_succ (n := e + 1)]

theorem sigma_val : ∀ f : PF, FactOK f → sigma 1 (val f) = sigF f
  | [], _ => by simp [val, sigF]
  | pe :: r, h => by
    simp only [val, sigF]
    rw [isMultiplicative_sigma.map_mul_of_coprime (coprime_head pe r h),
      sigma_one_apply_prime_pow (h.2 pe List.mem_cons_self), gsum_eq, sigma_val r h.tail]

theorem card_divisors_val : ∀ f : PF, FactOK f → (val f).divisors.card = ndF f
  | [], _ => by simp [val, ndF]
  | pe :: r, h => by
    rw [← sigma_zero_apply]
    simp only [val, ndF]
    rw [isMultiplicative_sigma.map_mul_of_coprime (coprime_head pe r h),
      sigma_zero_apply_prime_pow (h.2 pe List.mem_cons_self), sigma_zero_apply,
      card_divisors_val r h.tail]

theorem totient_val : ∀ f : PF, FactOK f → (∀ pe ∈ f, 0 < pe.2) → Nat.totient (val f) = phiF f
  | [], _, _ => by simp [val, phiF]
  | pe :: r, h, he => by
    simp only [val, phiF]
    rw [Nat.totient_mul (coprime_head pe r h),
      Nat.totient_prime_pow (h.2 pe List.mem_cons_self) (he pe List.mem_cons_self),
      totient_val r h.tail (fun q hq => he q (List.mem_cons_of_mem _ hq))]

theorem unitary_val : ∀ f : PF, FactOK f → ∀ d, d ∣ val f → Nat.Coprime d (val f / d) →
    ∃ s : PF, s.Sublist f ∧ d = val s
  | [], _, d, hd, _ => ⟨[], List.Sublist.slnil, by simpa [val] using hd⟩
  | pe :: r, h, d, hd, hu => by
    obtain ⟨p, e⟩ := pe
    have hp : p.Prime := h.2 (p, e) List.mem_cons_self
    have hcop : Nat.Coprime (p ^ e) (val r) := coprime_head (p, e) r h
    have hn : val ((p, e) :: r) = p ^ e * val r := rfl
    rw [hn] at hd hu
    have hpos : 0 < p ^ e * val r := Nat.mul_pos (pow_pos hp.pos _) (val_pos r h.tail)
    set d1 := Nat.gcd d (p ^ e)
    set d2 := Nat.gcd d (val r)
    have hdd : d = d1 * d2 := by
      rw [← Nat.Coprime.gcd_mul d hcop, Nat.gcd_eq_left hd]
    obtain ⟨j, hj, hd1'⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right d (p ^ e))
    have hd1 : d1 = p ^ j := hd1'
    have hd2m : d2 ∣ val r := Nat.gcd_dvd_right _ _
    obtain ⟨c, hc⟩ := hd2m
    have hquot : p ^ e * val r / d = p ^ (e - j) * c := by
      have : p ^ e * val r = d * (p ^ (e - j) * c) := by
        rw [hdd, hd1]
        conv_lhs => rw [hc, show p ^ e = p ^ j * p ^ (e - j) by
          rw [← pow_add]; congr 1; omega]
        ring
      rw [this, Nat.mul_div_cancel_left]
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · rw [h0, zero_mul] at this; omega
      · exact h0
    rw [hquot] at hu
    have hj' : j = 0 ∨ j = e := by
      by_contra hne
      push Not at hne
      have h1 : p ∣ d := by
        rw [hdd, hd1]
        exact Dvd.dvd.mul_right (dvd_pow_self p hne.1) _
      have h2 : p ∣ p ^ (e - j) * c :=
        Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.coprime_dvd_left h1 hu) h2
    have hu2 : Nat.Coprime d2 (val r / d2) := by
      have hd2pos : 0 < d2 := Nat.gcd_pos_of_pos_right _ (val_pos r h.tail)
      have : val r / d2 = c := by rw [hc, Nat.mul_div_cancel_left _ hd2pos]
      rw [this]
      exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left d _)
        (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) hu)
    obtain ⟨s, hs, hds⟩ := unitary_val r h.tail d2 ⟨c, hc⟩ hu2
    rcases hj' with rfl | rfl
    · refine ⟨s, List.Sublist.cons _ hs, ?_⟩
      rw [hdd, hd1, hds]; simp
    · exact ⟨(p, j) :: s, List.Sublist.cons_cons _ hs, by rw [hdd, hd1, hds]; rfl⟩

end OpenProblemsLib.ArithFactor
