import Mathlib.NumberTheory.LucasPrimality
import OpenProblemsLib.PowMod

/-!
# Pratt (Lucas) primality certificates, checked by the kernel

A certificate is a list of steps. A step `⟨p, a, [(q₁, k₁), …]⟩` claims that `p` is prime
with witness `a`: `p - 1 = ∏ qᵢ ^ kᵢ`, `a ^ (p - 1) ≡ 1 (mod p)` and
`a ^ ((p - 1) / qᵢ) ≢ 1 (mod p)` for every `i`. Each `qᵢ` must be the `p` of an earlier step
(so the list starts with `⟨2, 1, []⟩`). Soundness is Mathlib's `lucas_primality`.

All arithmetic in the checker is on literals (`powMod`, `*`, `/`, `%`, `==`), so
`prattCertifies n cert = true` is proved by `decide +kernel` even for large `n`.

Main results:
* `prime_of_prattCheck : prattCheck cert = true → ∀ s ∈ cert, s.p.Prime`
* `prime_of_prattCertifies : prattCertifies n cert = true → n.Prime`
* `primes_of_prattCertifiesAll : prattCertifiesAll ns cert = true → ∀ n ∈ ns, n.Prime`

`tools/pratt_cert.py` generates certificates.
-/

namespace OpenProblemsLib

/-- One step of a Pratt certificate: prime `p`, witness `a`, factorization of `p - 1` as
a list of (prime, exponent) pairs. -/
structure PrattStep where
  p : ℕ
  a : ℕ
  fs : List (ℕ × ℕ)

/-- `∏ q ^ k` over a factor list. -/
def factorsProd : List (ℕ × ℕ) → ℕ
  | [] => 1
  | qk :: r => qk.1 ^ qk.2 * factorsProd r

/-- The Lucas conditions for one step, given the list `ok` of already certified primes. -/
def stepOK (ok : List ℕ) (s : PrattStep) : Bool :=
  (2 ≤ s.p) && (factorsProd s.fs == s.p - 1) && (powMod s.a (s.p - 1) s.p == 1) &&
    s.fs.all (fun qk => ok.contains qk.1 && !(powMod s.a ((s.p - 1) / qk.1) s.p == 1))

/-- Check the steps in order, accumulating the certified primes. -/
def prattCheckAux : List ℕ → List PrattStep → Bool
  | _, [] => true
  | ok, s :: rest => stepOK ok s && prattCheckAux (s.p :: ok) rest

def prattCheck (cert : List PrattStep) : Bool := prattCheckAux [] cert

/-- `cert` is a valid certificate and certifies `n`. -/
def prattCertifies (n : ℕ) (cert : List PrattStep) : Bool :=
  prattCheck cert && cert.any (fun s => s.p == n)

/-- `cert` is a valid certificate and certifies every element of `ns`. -/
def prattCertifiesAll (ns : List ℕ) (cert : List PrattStep) : Bool :=
  prattCheck cert && ns.all (fun n => cert.any (fun s => s.p == n))

theorem exists_mem_of_prime_dvd_factorsProd :
    ∀ (fs : List (ℕ × ℕ)), (∀ qk ∈ fs, qk.1.Prime) →
      ∀ r : ℕ, r.Prime → r ∣ factorsProd fs → ∃ qk ∈ fs, qk.1 = r
  | [], _, r, hr, h => absurd h (hr.not_dvd_one)
  | qk :: rest, hfs, r, hr, h => by
    simp only [factorsProd] at h
    rcases (Nat.Prime.dvd_mul hr).mp h with h1 | h1
    · have hq : qk.1.Prime := hfs qk (by simp)
      have := (Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow h1)
      exact ⟨qk, by simp, this.symm⟩
    · obtain ⟨qk', hmem, he⟩ :=
        exists_mem_of_prime_dvd_factorsProd rest (fun x hx => hfs x (by simp [hx])) r hr h1
      exact ⟨qk', by simp [hmem], he⟩

/-- `powMod a e p = 1` with `2 ≤ p` is `(a : ZMod p) ^ e = 1`. -/
theorem zmod_pow_eq_one_iff (a e p : ℕ) (hp : 2 ≤ p) :
    ((a : ZMod p) ^ e = 1) ↔ powMod a e p = 1 := by
  rw [powMod_eq, ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt (show 1 < p by omega)]

theorem prime_of_stepOK (ok : List ℕ) (hok : ∀ q ∈ ok, q.Prime) (s : PrattStep)
    (h : stepOK ok s = true) : s.p.Prime := by
  simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hp2, hprod⟩, hpow⟩, hall⟩ := h
  have hfs : ∀ qk ∈ s.fs, qk.1.Prime := fun qk hqk => hok _ (hall qk hqk).1
  refine lucas_primality s.p (s.a : ZMod s.p) ((zmod_pow_eq_one_iff _ _ _ hp2).mpr hpow) ?_
  intro q hq hdvd hq1
  rw [← hprod] at hdvd
  obtain ⟨qk, hmem, rfl⟩ := exists_mem_of_prime_dvd_factorsProd s.fs hfs q hq hdvd
  exact (hall qk hmem).2 ((zmod_pow_eq_one_iff _ _ _ hp2).mp hq1)

theorem prime_of_prattCheckAux : ∀ (ok : List ℕ) (cert : List PrattStep),
    (∀ q ∈ ok, q.Prime) → prattCheckAux ok cert = true → ∀ s ∈ cert, s.p.Prime
  | _, [], _, _, s, hs => absurd hs (by simp)
  | ok, t :: rest, hok, h, s, hs => by
    simp only [prattCheckAux, Bool.and_eq_true] at h
    have ht : t.p.Prime := prime_of_stepOK ok hok t h.1
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact ht
    · refine prime_of_prattCheckAux (t.p :: ok) rest ?_ h.2 s hs'
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact ht
      · exact hok q hq'

theorem prime_of_prattCheck (cert : List PrattStep) (h : prattCheck cert = true) :
    ∀ s ∈ cert, s.p.Prime :=
  prime_of_prattCheckAux [] cert (by simp) h

theorem prime_of_prattCertifies (n : ℕ) (cert : List PrattStep)
    (h : prattCertifies n cert = true) : n.Prime := by
  simp only [prattCertifies, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨hc, s, hs, rfl⟩ := h
  exact prime_of_prattCheck cert hc s hs

theorem primes_of_prattCertifiesAll (ns : List ℕ) (cert : List PrattStep)
    (h : prattCertifiesAll ns cert = true) : ∀ n ∈ ns, n.Prime := by
  simp only [prattCertifiesAll, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    beq_iff_eq] at h
  intro n hn
  obtain ⟨s, hs, rfl⟩ := h.2 n hn
  exact prime_of_prattCheck cert h.1 s hs

end OpenProblemsLib
