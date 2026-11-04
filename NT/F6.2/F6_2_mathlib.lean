import Mathlib

/-
NT-F6.2 (Mathlib). Guy F6 (Lehmer): Q(a, b, c) is the least R such that for all sufficiently
large primes p some r ≤ R has r, r + a, r + b, r + c all quadratic residues mod p (∞ if there
is no such R). README result: Q(1,6,7), Q(1,6,10), Q(1,7,10), Q(5,6,9), Q(6,7,10) are all ∞.

Main theorem `F6_2_main`: for each of the five patterns P = {0,1,6,7}, {0,1,6,10},
{0,1,7,10}, {0,5,6,9}, {0,6,7,10} and all R, N there is a prime p > N such that for every
r ≤ R (r = 0 included, which only strengthens the claim) some r + a (a ∈ P) is not a square mod p (Mathlib `IsSquare` in `ZMod p`;
so it is not a quadratic residue under either convention for 0). `F6_2_Q_infinite`: hence no
R works for all sufficiently large primes, i.e. Q = ∞ for all five.

Proof. Dirichlet's theorem (Mathlib `Nat.forall_exists_prime_gt_and_modEq`) and the Jacobi
symbol (Mathlib `jacobiSym`):
* {0,1,6,7}, {0,1,7,10}: take p ≡ 3 (mod 4) and p ≡ 1 (mod every odd n ≤ R + 10); by
  reciprocity (`jacobiSym.quadratic_reciprocity_three_mod_four`) (n/p) = -1 for n ≡ 3 (mod 4),
  n ≤ R + 10, and every r + P contains such an n (two odd elements differing by 2 mod 4).
* {0,1,6,10}, {0,5,6,9} (q = 11), {0,6,7,10} (q = 19): take p ≡ q modulo 4·∏{n ≤ R + 10,
  q ∤ n}; then (n/p) = (n/q) for those n (`jacobiSym.mod_right'`), and every translate of P
  mod q meets a nonzero non-residue class (kernel check).

Outside Lean: nothing.
-/

open Finset

/-- Some element of r + P is a non-square mod p. -/
def Blocked (p : ℕ) (P : List ℕ) (r : ℕ) : Prop := ∃ a ∈ P, ¬ IsSquare (((r + a : ℕ)) : ZMod p)

theorem nonsq_of_jacobi (p n : ℕ) (hp : p.Prime) (h : jacobiSym n p = -1) :
    ¬ IsSquare ((n : ℕ) : ZMod p) := by
  have := Fact.mk hp
  rw [← legendreSym.eq_neg_one_iff', jacobiSym.legendreSym.to_jacobiSym]
  exact_mod_cast h

/-- χ₋₄ transfer: primes p with (n/p) = -1 for all n ≤ X, n ≡ 3 (mod 4). -/
theorem chi_transfer (X N : ℕ) :
    ∃ p > N, p.Prime ∧ ∀ n, n ≤ X → n % 4 = 3 → jacobiSym n p = -1 := by
  set L := ∏ n ∈ (Ico 1 (X + 1)).filter Odd, n with hL
  have hLodd : Odd L := Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one
    (fun n hn => (mem_filter.mp hn).2)
  obtain ⟨k, hk⟩ := hLodd
  have hcop : Nat.Coprime (2 * L + 1) (4 * L) := by
    apply Nat.Coprime.mul_right
    · rw [show 4 = 2 ^ 2 by rfl]
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_two_right]; exact ⟨L, rfl⟩
    · rw [Nat.coprime_comm, show 2 * L + 1 = 1 + L * 2 by ring, Nat.coprime_add_mul_left_right]
      exact Nat.coprime_one_right L
  obtain ⟨p, hpN, hp, hpm⟩ := Nat.forall_exists_prime_gt_and_modEq N (by omega) hcop
  refine ⟨p, hpN, hp, fun n hnX hn3 => ?_⟩
  have hp4 : p % 4 = 3 := by
    have := (Nat.ModEq.of_dvd (dvd_mul_right 4 L) hpm)
    unfold Nat.ModEq at this; omega
  have hn0 : 1 ≤ n := by omega
  have hnL : n ∣ L := Finset.dvd_prod_of_mem _ (mem_filter.mpr
    ⟨mem_Ico.mpr ⟨hn0, by omega⟩, Nat.odd_iff.mpr (by omega)⟩)
  have hpn : p % n = 1 % n := by
    have h1 := Nat.ModEq.of_dvd (Dvd.dvd.mul_left hnL 4) hpm
    unfold Nat.ModEq at h1
    rw [h1]
    obtain ⟨j, hj⟩ := hnL
    rw [hj, show 2 * (n * j) + 1 = 1 + n * (2 * j) by ring, Nat.add_mul_mod_self_left]
  rw [jacobiSym.quadratic_reciprocity_three_mod_four hn3 hp4, jacobiSym.mod_left]
  have : ((p : ℤ) % (n : ℤ)) = ((1 % n : ℕ) : ℤ) := by rw [← hpn]; push_cast; rfl
  rw [this]
  rcases Nat.lt_or_ge n 2 with h | h
  · omega
  · rw [Nat.mod_eq_of_lt h]; simp [jacobiSym.one_left]

/-- Legendre transfer: for an odd prime q, primes p with (n/p) = (n/q) for all n ≤ X, q ∤ n. -/
theorem leg_transfer (q X N : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    ∃ p > N, p.Prime ∧ ∀ n, 1 ≤ n → n ≤ X → ¬ q ∣ n → jacobiSym n p = jacobiSym n q := by
  set L := ∏ n ∈ (Ico 1 (X + 1)).filter (fun n => ¬ q ∣ n), n with hL
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hcop : Nat.Coprime q (4 * L) := by
    apply Nat.Coprime.mul_right
    · rw [show 4 = 2 ^ 2 by rfl]
      exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hqodd)
    · apply Nat.Coprime.prod_right
      intro n hn
      exact (Nat.Prime.coprime_iff_not_dvd hq).mpr (mem_filter.mp hn).2
  have hL0 : L ≠ 0 := by
    rw [hL, Finset.prod_ne_zero_iff]
    intro n hn; have := (mem_Ico.mp (mem_filter.mp hn).1).1; omega
  obtain ⟨p, hpN, hp, hpm⟩ := Nat.forall_exists_prime_gt_and_modEq N (by omega) hcop
  refine ⟨p, hpN, hp, fun n hn1 hnX hqn => ?_⟩
  have hnL : n ∣ L := Finset.dvd_prod_of_mem _ (mem_filter.mpr
    ⟨mem_Ico.mpr ⟨hn1, by omega⟩, hqn⟩)
  have h4n := Nat.ModEq.of_dvd (mul_dvd_mul_left 4 hnL) hpm
  have hpodd : Odd p := by
    have := Nat.ModEq.of_dvd (dvd_mul_right 4 L) hpm
    unfold Nat.ModEq at this
    rw [Nat.odd_iff] at hqodd ⊢; omega
  rw [jacobiSym.mod_right' n hpodd, jacobiSym.mod_right' n hqodd]
  unfold Nat.ModEq at h4n
  rw [h4n]

/-- `c` is a nonzero non-square mod q (c < q). -/
def isNR (q c : ℕ) : Bool := c != 0 && (List.range q).all (fun x => x * x % q != c)

/-- Every translate of P mod q meets a nonzero non-residue class. -/
def blockedQ (q : ℕ) (P : List ℕ) : Bool :=
  (List.range q).all (fun t => P.any (fun s => isNR q ((t + s) % q)))

theorem jacobi_of_isNR (q n : ℕ) (hq : q.Prime) (h : isNR q (n % q) = true) :
    jacobiSym n q = -1 ∧ ¬ q ∣ n := by
  have := Fact.mk hq
  simp only [isNR, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_range] at h
  refine ⟨?_, fun hd => h.1 (Nat.mod_eq_zero_of_dvd hd)⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have e : ((n : ℤ) : ZMod q) = ((n % q : ℕ) : ZMod q) := by simp
  rw [legendreSym.eq_neg_one_iff, e]
  rintro ⟨x, hx⟩
  apply h.2 x.val (ZMod.val_lt x)
  have : ((x.val * x.val : ℕ) : ZMod q) = ((n % q : ℕ) : ZMod q) := by
    push_cast; rw [ZMod.natCast_zmod_val, hx]
  rw [ZMod.natCast_eq_natCast_iff'] at this
  rw [this, Nat.mod_mod]

theorem by_leg (q : ℕ) (P : List ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hP : ∀ a ∈ P, a ≤ 10)
    (hb : blockedQ q P = true) (R N : ℕ) :
    ∃ p > N, p.Prime ∧ ∀ r, r ≤ R → Blocked p P r := by
  obtain ⟨p, hpN, hp, hJ⟩ := leg_transfer q (R + 10) N hq hq2
  refine ⟨p, hpN, hp, fun r hrR => ?_⟩
  have := List.all_eq_true.mp hb (r % q) (List.mem_range.mpr (Nat.mod_lt _ hq.pos))
  obtain ⟨s, hs, hnr⟩ := List.any_eq_true.mp this
  have hmod : (r % q + s) % q = (r + s) % q := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [hmod] at hnr
  obtain ⟨hj, hqd⟩ := jacobi_of_isNR q (r + s) hq hnr
  refine ⟨s, hs, nonsq_of_jacobi p (r + s) hp ?_⟩
  rw [hJ (r + s) (Nat.pos_of_ne_zero (fun h0 => hqd (h0 ▸ dvd_zero q)))
    (by have := hP s hs; omega) hqd, hj]

theorem by_chi (P : List ℕ) (hP : ∀ a ∈ P, a ≤ 10)
    (hc : ∀ r, ∃ a ∈ P, (r + a) % 4 = 3) (R N : ℕ) :
    ∃ p > N, p.Prime ∧ ∀ r, r ≤ R → Blocked p P r := by
  obtain ⟨p, hpN, hp, hJ⟩ := chi_transfer (R + 10) N
  refine ⟨p, hpN, hp, fun r hrR => ?_⟩
  obtain ⟨a, ha, h3⟩ := hc r
  exact ⟨a, ha, nonsq_of_jacobi p (r + a) hp (hJ _ (by have := hP a ha; omega) h3)⟩

def P1 : List ℕ := [0, 1, 6, 7]
def P2 : List ℕ := [0, 1, 6, 10]
def P3 : List ℕ := [0, 1, 7, 10]
def P4 : List ℕ := [0, 5, 6, 9]
def P5 : List ℕ := [0, 6, 7, 10]

theorem F6_2_main : ∀ P ∈ [P1, P2, P3, P4, P5], ∀ R N : ℕ,
    ∃ p > N, p.Prime ∧ ∀ r, r ≤ R → Blocked p P r := by
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl
  · exact by_chi P1 (by decide) (fun r => by
      rcases Nat.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
      · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
        · exact ⟨7, by decide, by omega⟩
        · exact ⟨1, by decide, by omega⟩
      · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
        · exact ⟨6, by decide, by omega⟩
        · exact ⟨0, by decide, by omega⟩)
  · exact by_leg 11 P2 (by norm_num) (by norm_num) (by decide) (by decide)
  · exact by_chi P3 (by decide) (fun r => by
      rcases Nat.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
      · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
        · exact ⟨7, by decide, by omega⟩
        · exact ⟨1, by decide, by omega⟩
      · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
        · exact ⟨10, by decide, by omega⟩
        · exact ⟨0, by decide, by omega⟩)
  · exact by_leg 11 P4 (by norm_num) (by norm_num) (by decide) (by decide)
  · exact by_leg 19 P5 (by norm_num) (by norm_num) (by decide) (by decide)

/-- Q(P) = ∞: no R serves all sufficiently large primes. -/
theorem F6_2_Q_infinite : ∀ P ∈ [P1, P2, P3, P4, P5],
    ¬ ∃ R N : ℕ, ∀ p, p.Prime → N < p →
      ∃ r, r ≤ R ∧ ∀ a ∈ P, IsSquare (((r + a : ℕ)) : ZMod p) := by
  intro P hP ⟨R, N, h⟩
  obtain ⟨p, hpN, hp, hb⟩ := F6_2_main P hP R N
  obtain ⟨r, h2, hall⟩ := h p hp hpN
  obtain ⟨a, ha, hns⟩ := hb r h2
  exact hns (hall a ha)
