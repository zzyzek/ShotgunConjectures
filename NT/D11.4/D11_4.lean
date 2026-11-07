/-
NT-D11.4 (Guy, UPINT 3rd ed., D11): "Is 48 the minimum number of squarefree
integers with exactly two prime factors whose reciprocals sum to 1?"  No.

Witness (T. Watanabe, Prime Puzzles & Problems, Puzzle 899): 47 distinct
numbers p*q (p < q primes) with reciprocal sum 1.

Checked here (core Lean, no Mathlib, `decide`):
* `D11_4_main`: the 47 listed numbers are pairwise distinct, each equals
  p*q for an explicit pair of primes p < q (`IsPrime` is the usual
  definition, derived from a bounded trial-division check by
  `isPrimeSmall_sound`), and the sum of their reciprocals in `Rat` is 1.
* `D11_4_not_min`: hence a set of fewer than 48 such numbers exists.
Not checked here: whether 46 or fewer terms are possible (Watanabe's
claimed computer proof that 47 is the minimum is not reproduced).
-/

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

def isPrimeSmall (p : Nat) : Bool :=
  2 ≤ p && (List.range p).all (fun d => d < 2 || p % d != 0)

theorem isPrimeSmall_sound (p : Nat) (h : isPrimeSmall p = true) : IsPrime p := by
  simp only [isPrimeSmall, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨h2, hall⟩ := h
  refine ⟨h2, fun m hm => ?_⟩
  have hp : 0 < p := by omega
  have hle : m ≤ p := Nat.le_of_dvd hp hm
  by_cases hmp : m = p
  · exact Or.inr hmp
  · have hlt : m < p := by omega
    rcases hall m hlt with h1 | h1
    · have : m ≠ 0 := by
        intro h0; subst h0; rw [Nat.zero_dvd] at hm; omega
      left; omega
    · exact absurd (Nat.mod_eq_zero_of_dvd hm) h1

/-- Squarefree with exactly two prime factors. -/
def IsSqfSemiprime (d : Nat) : Prop := ∃ p q, p < q ∧ IsPrime p ∧ IsPrime q ∧ d = p * q

/-- The 47 witnesses, as (p, q) with p < q. -/
def W : List (Nat × Nat) :=
  [(2,3),(2,5),(2,7),(3,5),(3,7),(2,11),(2,13),(3,11),(2,17),(5,7),(2,19),(3,13),
   (2,23),(3,17),(5,11),(3,19),(2,29),(2,31),(5,13),(3,23),(2,37),(2,41),(5,17),
   (2,43),(3,29),(7,13),(3,31),(5,19),(2,53),(3,37),(3,41),(7,19),(5,29),(5,31),
   (3,53),(5,37),(7,29),(5,43),(11,23),(5,53),(7,41),(11,29),(17,29),(11,53),
   (17,43),(23,37),(29,37)]

def S : List Nat := W.map (fun pq => pq.1 * pq.2)

theorem W_ok : W.all (fun pq => decide (pq.1 < pq.2) && isPrimeSmall pq.1 && isPrimeSmall pq.2) = true := by
  decide

theorem S_nodup : S.Nodup := by decide

theorem S_length : S.length = 47 := by decide

theorem S_sum : (S.map (fun d : Nat => (1 : Rat) / (d : Rat))).sum = 1 := by decide +kernel

theorem S_semiprime : ∀ d ∈ S, IsSqfSemiprime d := by
  intro d hd
  simp only [S, List.mem_map] at hd
  obtain ⟨⟨p, q⟩, hmem, rfl⟩ := hd
  have h := List.all_eq_true.mp W_ok (p, q) hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨p, q, h.1.1, isPrimeSmall_sound p h.1.2, isPrimeSmall_sound q h.2, rfl⟩

theorem D11_4_main :
    S.length = 47 ∧ S.Nodup ∧ (∀ d ∈ S, IsSqfSemiprime d) ∧
    (S.map (fun d : Nat => (1 : Rat) / (d : Rat))).sum = 1 :=
  ⟨S_length, S_nodup, S_semiprime, S_sum⟩

theorem D11_4_not_min :
    ∃ T : List Nat, T.length < 48 ∧ T.Nodup ∧ (∀ d ∈ T, IsSqfSemiprime d) ∧
      (T.map (fun d : Nat => (1 : Rat) / (d : Rat))).sum = 1 :=
  ⟨S, by rw [S_length]; decide, S_nodup, S_semiprime, S_sum⟩
