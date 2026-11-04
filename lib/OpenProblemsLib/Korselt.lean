import Mathlib.NumberTheory.CarmichaelNumber
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.List.Prime
import OpenProblemsLib.Pratt
import OpenProblemsLib.Fermat

/-!
# Carmichael numbers and Korselt's criterion, with kernel-checkable instances

Mathlib's `Nat.IsCarmichael n` is `2 < n ∧ ¬ n.Prime ∧ ∀ b, b.Coprime n → ProbablePrime n b`
(`ProbablePrime n b` is `n ∣ b ^ (n - 1) - 1`), and Mathlib proves Korselt's criterion
`Nat.isCarmichael_iff_korselt` (both directions; the forward direction uses that the unit
group of `ZMod (p ^ 2)` is cyclic). This file adds:

* `isCarmichael_iff_modEq`: the textbook definition (composite, `a ^ (n - 1) ≡ 1 (mod n)`
  for every `a` coprime to `n`) is `Nat.IsCarmichael`.
* `korselt`, `korselt_necessary` (`p ∣ n` prime ⇒ `p - 1 ∣ n - 1`), `IsCarmichael.squarefree'`.
* Factorization helpers: `squarefree_of_primes`, `mem_of_prime_dvd_prod`,
  `primeFactors_eq_of_primes`.
* `exists_sublist_of_dvd_prod`, `divisorsList`, `mem_divisorsList_of_dvd`: every divisor of a
  product of primes is a sub-product (for exhaustive divisor checks by `decide`).
* `isCarmichael_of_factors`: Korselt's sufficient condition for an explicit list of
  distinct primes.
* `dvd_sub_one_of_eq` (Korselt divisibility from an explicit quotient) and
  `not_isCarmichael_of_powMod` (a coprime base with `b ^ (n-1) ≢ 1` rules out Carmichael).
* `carmichaelCheck n ps cert : Bool` with `isCarmichael_of_carmichaelCheck`: the primes
  in `ps` are certified by the Pratt certificate `cert`, `ps` has no repeats,
  `ps.prod = n`, `2 ≤ ps.length`, `(n - 1) % (p - 1) = 0` for all `p ∈ ps`.
  Proved by `decide +kernel`.
-/

namespace OpenProblemsLib

open Nat

/-- Korselt's criterion (Mathlib `Nat.isCarmichael_iff_korselt`). -/
theorem korselt {n : ℕ} :
    n.IsCarmichael ↔ 2 < n ∧ ¬n.Prime ∧ Squarefree n ∧ ∀ p, p.Prime → p ∣ n → p - 1 ∣ n - 1 :=
  Nat.isCarmichael_iff_korselt

/-- Korselt's necessary condition: every prime divisor `p` of a Carmichael number `n`
has `p - 1 ∣ n - 1`. -/
theorem korselt_necessary {n p : ℕ} (h : n.IsCarmichael) (hp : p.Prime) (hpn : p ∣ n) :
    p - 1 ∣ n - 1 :=
  h.prime_sub_one_dvd hp hpn

/-- Carmichael numbers are squarefree. -/
theorem IsCarmichael.squarefree' {n : ℕ} (h : n.IsCarmichael) : Squarefree n := h.squarefree

/-- The textbook definition: `n` is Carmichael iff it is composite (and `> 2`) and
`a ^ (n - 1) ≡ 1 (mod n)` for every `a` coprime to `n`. -/
theorem isCarmichael_iff_modEq {n : ℕ} :
    n.IsCarmichael ↔ 2 < n ∧ ¬n.Prime ∧ ∀ a, a.Coprime n → a ^ (n - 1) ≡ 1 [MOD n] := by
  constructor
  · rintro ⟨h2, hp, h⟩
    refine ⟨h2, hp, fun a ha => ?_⟩
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · simp at ha; omega
      · exact h
    exact (Nat.probablePrime_iff_modEq n ha1).mp (h a ha)
  · rintro ⟨h2, hp, h⟩
    refine ⟨h2, hp, fun a ha => ?_⟩
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · simp at ha; omega
      · exact h
    exact (Nat.probablePrime_iff_modEq n ha1).mpr (h a ha)

/-- A product of distinct primes is squarefree. -/
theorem squarefree_of_primes (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime) (hnd : ps.Nodup) :
    Squarefree ps.prod := by
  have h0 : ps.prod ≠ 0 := by
    rw [Ne, List.prod_eq_zero_iff]
    intro h; exact (hp 0 h).ne_zero rfl
  rw [Nat.squarefree_iff_nodup_primeFactorsList h0]
  exact (Nat.primeFactorsList_unique rfl hp).nodup_iff.mp hnd

/-- A prime dividing a product of primes is one of them. -/
theorem mem_of_prime_dvd_prod (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime) {q : ℕ} (hq : q.Prime)
    (h : q ∣ ps.prod) : q ∈ ps := by
  obtain ⟨a, ha, hqa⟩ := (Nat.Prime.prime hq).dvd_prod_iff.mp h
  rwa [(Nat.prime_dvd_prime_iff_eq hq (hp a ha)).mp hqa]

/-- The prime factors of a product of primes are exactly those primes. -/
theorem primeFactors_eq_of_primes (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime) :
    ps.prod.primeFactors = ps.toFinset := by
  ext q
  simp only [Nat.mem_primeFactors, List.mem_toFinset]
  constructor
  · rintro ⟨hq, hdvd, _⟩; exact mem_of_prime_dvd_prod ps hp hq hdvd
  · intro hq
    refine ⟨hp q hq, List.dvd_prod hq, ?_⟩
    rw [Ne, List.prod_eq_zero_iff]
    intro h; exact (hp 0 h).ne_zero rfl

/-- Every divisor of a product of primes is the product of a sublist. -/
theorem exists_sublist_of_dvd_prod : ∀ (ps : List ℕ), (∀ p ∈ ps, p.Prime) →
    ∀ d : ℕ, d ∣ ps.prod → ∃ s : List ℕ, s.Sublist ps ∧ d = s.prod
  | [], _, d, h => ⟨[], List.Sublist.slnil, by simpa using h⟩
  | p :: t, hp, d, h => by
    have hpp : p.Prime := hp p (by simp)
    have ht : ∀ q ∈ t, q.Prime := fun q hq => hp q (by simp [hq])
    rw [List.prod_cons] at h
    by_cases hpd : p ∣ d
    · obtain ⟨e, rfl⟩ := hpd
      have he : e ∣ t.prod := (Nat.mul_dvd_mul_iff_left hpp.pos).mp h
      obtain ⟨s, hs, rfl⟩ := exists_sublist_of_dvd_prod t ht e he
      exact ⟨p :: s, hs.cons_cons p, by simp⟩
    · have hc : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hpd
      have he : d ∣ t.prod := hc.symm.dvd_of_dvd_mul_left h
      obtain ⟨s, hs, rfl⟩ := exists_sublist_of_dvd_prod t ht d he
      exact ⟨s, hs.cons p, rfl⟩

/-- The divisors of `ps.prod` (as a list, possibly with repeats) when `ps` are primes. -/
def divisorsList (ps : List ℕ) : List ℕ := ps.sublists.map List.prod

theorem mem_divisorsList_of_dvd (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime) {d : ℕ}
    (h : d ∣ ps.prod) : d ∈ divisorsList ps := by
  obtain ⟨s, hs, rfl⟩ := exists_sublist_of_dvd_prod ps hp d h
  exact List.mem_map.mpr ⟨s, List.mem_sublists.mpr hs, rfl⟩

/-- Korselt's sufficient condition for an explicit factorization into distinct primes. -/
theorem isCarmichael_of_factors (n : ℕ) (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hnd : ps.Nodup) (hprod : ps.prod = n) (hlen : 2 ≤ ps.length)
    (hdvd : ∀ p ∈ ps, p - 1 ∣ n - 1) : n.IsCarmichael := by
  match ps, hp, hnd, hprod, hlen, hdvd with
  | a :: b :: t, hp, hnd, hprod, _, hdvd =>
    have ha := hp a (by simp)
    have hb := hp b (by simp)
    have ht : 1 ≤ t.prod := by
      apply Nat.one_le_iff_ne_zero.mpr
      rw [Ne, List.prod_eq_zero_iff]
      intro h; exact (hp 0 (by simp [h])).ne_zero rfl
    have hbt : 2 ≤ b * t.prod := le_trans hb.two_le (Nat.le_mul_of_pos_right _ ht)
    have hn : n = a * (b * t.prod) := by rw [← hprod]; simp
    refine korselt.mpr ⟨?_, ?_, ?_, ?_⟩
    · rw [hn]; nlinarith [ha.two_le]
    · rw [hn]; exact Nat.not_prime_mul (by have := ha.two_le; omega) (by omega)
    · rw [← hprod]; exact squarefree_of_primes _ hp hnd
    · intro q hq hqn
      exact hdvd q (mem_of_prime_dvd_prod _ hp hq (hprod ▸ hqn))

/-- `f - 1 ∣ N - 1` from an explicit quotient (for polynomial Korselt identities). -/
theorem dvd_sub_one_of_eq {N f Q : ℕ} (h : N = (f - 1) * Q + 1) : f - 1 ∣ N - 1 := by
  rw [h, Nat.add_sub_cancel]; exact Dvd.intro _ rfl

/-- A coprime base `b` with `b ^ (n - 1) ≢ 1 (mod n)` shows that `n` is not Carmichael. -/
theorem not_isCarmichael_of_powMod (n b : ℕ) (hb : Nat.Coprime b n) (hn : 2 ≤ n)
    (h : powMod b (n - 1) n ≠ 1) : ¬ n.IsCarmichael := by
  intro hc
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | hpos
    · simp at hb; omega
    · exact hpos
  exact h ((probablePrime_iff_powMod n b hb1 hn).mp (hc.probablePrime_of_coprime hb))

/-- Bool check of Korselt's sufficient condition, with primality by a Pratt certificate. -/
def carmichaelCheck (n : ℕ) (ps : List ℕ) (cert : List PrattStep) : Bool :=
  prattCertifiesAll ps cert && decide ps.Nodup && (ps.prod == n) && (2 ≤ ps.length) &&
    ps.all (fun p => (n - 1) % (p - 1) == 0)

theorem isCarmichael_of_carmichaelCheck (n : ℕ) (ps : List ℕ) (cert : List PrattStep)
    (h : carmichaelCheck n ps cert = true) : n.IsCarmichael := by
  simp only [carmichaelCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hc, hnd⟩, hprod⟩, hlen⟩, hdvd⟩ := h
  exact isCarmichael_of_factors n ps (primes_of_prattCertifiesAll ps cert hc) hnd hprod hlen
    (fun p hp => Nat.dvd_of_mod_eq_zero (hdvd p hp))

/-- Bool check that `n` is the product of the distinct certified primes `ps`. -/
def factorCheck (n : ℕ) (ps : List ℕ) (cert : List PrattStep) : Bool :=
  prattCertifiesAll ps cert && decide ps.Nodup && (ps.prod == n)

theorem of_factorCheck (n : ℕ) (ps : List ℕ) (cert : List PrattStep)
    (h : factorCheck n ps cert = true) :
    (∀ p ∈ ps, p.Prime) ∧ ps.Nodup ∧ ps.prod = n := by
  simp only [factorCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨primes_of_prattCertifiesAll ps cert h.1.1, h.1.2, h.2⟩

/-- From `factorCheck`: `n` is squarefree with prime factor set `ps`. -/
theorem squarefree_of_factorCheck (n : ℕ) (ps : List ℕ) (cert : List PrattStep)
    (h : factorCheck n ps cert = true) : Squarefree n ∧ n.primeFactors = ps.toFinset := by
  obtain ⟨hp, hnd, hprod⟩ := of_factorCheck n ps cert h
  subst hprod
  exact ⟨squarefree_of_primes ps hp hnd, primeFactors_eq_of_primes ps hp⟩

end OpenProblemsLib
