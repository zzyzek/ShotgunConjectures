import Mathlib.NumberTheory.FermatPsp
import OpenProblemsLib.PowMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# Fermat pseudoprimes from a `powMod` computation

Mathlib: `Nat.ProbablePrime n b := n ∣ b ^ (n - 1) - 1` and
`Nat.FermatPsp n b := ProbablePrime n b ∧ ¬ n.Prime ∧ 1 < n`.

* `probablePrime_iff_powMod`: for `1 ≤ b`, `2 ≤ n`: `ProbablePrime n b ↔ powMod b (n-1) n = 1`.
* `pspCheck n b d : Bool` (`d` a proper divisor showing `n` composite) and
  `fermatPsp_of_pspCheck`; proved by `decide +kernel`.
* `not_fermatPsp_of_powMod`: `powMod b (n - 1) n ≠ 1` rules out `FermatPsp n b`.
* `prime_dvd_pow_gcd_sub_one`: Fermat + order argument: a prime `p ∣ N` with `p ∤ b` and
  `N` a probable prime to base `b` divides `b ^ gcd(p - 1, N - 1) - 1`;
  `prime_dvd_pow_sub_one_of_gcd_dvd`: hence `p ∣ b ^ m - 1` whenever `gcd(p-1, N-1) ∣ m`.
-/

namespace OpenProblemsLib

theorem probablePrime_iff_powMod (n b : ℕ) (hb : 1 ≤ b) (hn : 2 ≤ n) :
    n.ProbablePrime b ↔ powMod b (n - 1) n = 1 := by
  rw [Nat.probablePrime_iff_modEq n hb, Nat.ModEq, powMod_eq,
    Nat.mod_eq_of_lt (show 1 < n by omega)]

/-- `n` is a Fermat pseudoprime to base `b`, with `d` a proper divisor of `n`. -/
def pspCheck (n b d : ℕ) : Bool :=
  (1 ≤ b) && (2 ≤ d) && (d < n) && (n % d == 0) && (powMod b (n - 1) n == 1)

theorem fermatPsp_of_pspCheck (n b d : ℕ) (h : pspCheck n b d = true) : n.FermatPsp b := by
  simp only [pspCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hb, hd2⟩, hdn⟩, hmod⟩, hpow⟩ := h
  refine ⟨(probablePrime_iff_powMod n b hb (by omega)).mpr hpow, ?_, by omega⟩
  exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hmod) hd2 hdn

/-- `n` is a probable prime to base `b` (no compositeness claim). -/
def probablePrimeCheck (n b : ℕ) : Bool := (1 ≤ b) && (2 ≤ n) && (powMod b (n - 1) n == 1)

theorem probablePrime_of_check (n b : ℕ) (h : probablePrimeCheck n b = true) :
    n.ProbablePrime b := by
  simp only [probablePrimeCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact (probablePrime_iff_powMod n b h.1.1 h.1.2).mpr h.2

theorem not_probablePrime_of_powMod (n b : ℕ) (hb : 1 ≤ b) (hn : 2 ≤ n)
    (h : powMod b (n - 1) n ≠ 1) : ¬ n.ProbablePrime b :=
  fun hp => h ((probablePrime_iff_powMod n b hb hn).mp hp)

theorem not_fermatPsp_of_powMod (n b : ℕ) (hb : 1 ≤ b) (hn : 2 ≤ n)
    (h : powMod b (n - 1) n ≠ 1) : ¬ n.FermatPsp b :=
  fun hp => not_probablePrime_of_powMod n b hb hn h hp.1

/-- Fermat's little theorem and `ord_p(b) ∣ N - 1`: a prime divisor `p` of a probable prime
`N` to base `b` (with `p ∤ b`) divides `b ^ gcd(p - 1, N - 1) - 1`. -/
theorem prime_dvd_pow_gcd_sub_one {p N b : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hpb : ¬ p ∣ b)
    (hN : N.ProbablePrime b) : p ∣ b ^ Nat.gcd (p - 1) (N - 1) - 1 := by
  have := Fact.mk hp
  have hb0 : (b : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hbpos : 1 ≤ b := Nat.pos_of_ne_zero (by rintro rfl; exact hpb (dvd_zero p))
  have h1 : (b : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hb0
  have h2 : (b : ZMod p) ^ (N - 1) = 1 := by
    have : p ∣ b ^ (N - 1) - 1 := dvd_trans hpN hN
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hbpos), sub_eq_zero] at this
    simpa using this
  have h3 : (b : ZMod p) ^ Nat.gcd (p - 1) (N - 1) = 1 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hbpos), sub_eq_zero]
  simpa using h3

theorem prime_dvd_pow_sub_one_of_gcd_dvd {p N b m : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hpb : ¬ p ∣ b) (hN : N.ProbablePrime b) (hg : Nat.gcd (p - 1) (N - 1) ∣ m) :
    p ∣ b ^ m - 1 :=
  dvd_trans (prime_dvd_pow_gcd_sub_one hp hpN hpb hN) (Nat.pow_sub_one_dvd_pow_sub_one b hg)

end OpenProblemsLib
