/-
OEIS A165640, Mathlib proof.

A165640(n) = number of multisets of n integers, each -2, +1 or +3, with sum
3 (offset 1). Conjecture: a(n) = floor(4(n+4)/5) - floor(2(n+4)/3).

Definitions: `A165640_ms n` counts the multisets of size n with elements in
{-2, 1, 3} and sum 3 (`Finset.sym`), the OEIS definition. `A165640 n`
counts multiplicity vectors (x, y, z) ∈ ℕ³ (x copies of -2, y of 1, z of 3)
with x + y + z = n and -2x + y + 3z = 3; `A165640_ms_eq` proves the two
counts equal.

Main theorems: `A165640_ms_main` (and `A165640_main` for the vector form):
for every n ≥ 1,
  A165640_ms n = 4(n+4)/5 - 2(n+4)/3   (natural-number floor division).
This is the README result (at n = 0 the formula gives 1, the count is 0).

Proof: z determines x and y; the admissible z are those with
z ≡ n (mod 3) and 5z ≤ 2n + 3 (and n + 2z ≥ 3), counted by
`Nat.count_modEq_card`; the final identity is linear arithmetic with floor
divisions (`omega`); n = 1, 2 by `decide`. Nothing is outside Lean.
-/
import Mathlib

/-- Multiplicity vectors (x, y, z) of n elements from {-2, 1, 3} with sum 3. -/
def A165640 (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p => p.1 + p.2.1 + p.2.2 = n ∧ -2 * (p.1 : ℤ) + p.2.1 + 3 * p.2.2 = 3)).card

/-- The count as a count of admissible z. -/
theorem A165640_eq_z (n : ℕ) :
    A165640 n = ((Finset.range (n + 1)).filter
      (fun z => (n + 2 * z) % 3 = 0 ∧ 3 ≤ n + 2 * z ∧ 5 * z ≤ 2 * n + 3)).card := by
  unfold A165640
  apply Finset.card_bij (fun p _ => p.2.2)
  · rintro ⟨x, y, z⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
    omega
  · rintro ⟨x, y, z⟩ h ⟨x', y', z'⟩ h' he
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h h'
    simp only at he
    subst he
    have : x = x' := by omega
    have : y = y' := by omega
    simp_all
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_range] at hz
    refine ⟨((n + 2 * z - 3) / 3, n - (n + 2 * z - 3) / 3 - z, z), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega

theorem A165640_main (n : ℕ) (hn : 1 ≤ n) : A165640 n = 4 * (n + 4) / 5 - 2 * (n + 4) / 3 := by
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · interval_cases n <;> decide
  · rw [A165640_eq_z]
    have hs : (Finset.range (n + 1)).filter
        (fun z => (n + 2 * z) % 3 = 0 ∧ 3 ≤ n + 2 * z ∧ 5 * z ≤ 2 * n + 3) =
        (Finset.range ((2 * n + 3) / 5 + 1)).filter (fun z => z ≡ n [MOD 3]) := by
      ext z
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_range, Nat.ModEq]
      have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      have h2 : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
      constructor
      · rintro ⟨_, ha, _, hb⟩
        refine ⟨by omega, by omega⟩
      · rintro ⟨ha, hb⟩
        refine ⟨by omega, by omega, by omega, by omega⟩
    rw [hs, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ (by norm_num)]
    have h15 : n % 15 < 15 := Nat.mod_lt _ (by norm_num)
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 15 ∧ n = 15 * q + r := ⟨n / 15, n % 15, h15, by omega⟩
    interval_cases r <;> split_ifs <;> omega

/-! ## Multisets -/

/-- A165640 from its definition: multisets of n integers from {-2, 1, 3} with sum 3
(`Finset.sym`: the multisets of size n with elements in the set). -/
def A165640_ms (n : ℕ) : ℕ :=
  ((({-2, 1, 3} : Finset ℤ).sym n).filter (fun s : Sym ℤ n => (s : Multiset ℤ).sum = 3)).card

/-- A multiset supported in {-2, 1, 3} is determined by its three multiplicities. -/
theorem A165640_decomp (m : Multiset ℤ) (hm : ∀ a ∈ m, a ∈ ({-2, 1, 3} : Finset ℤ)) :
    m = Multiset.replicate (m.count (-2)) (-2) + Multiset.replicate (m.count 1) 1 +
      Multiset.replicate (m.count 3) 3 := by
  ext a
  simp only [Multiset.count_add, Multiset.count_replicate]
  by_cases h1 : a = -2
  · subst h1; simp
  by_cases h2 : a = 1
  · subst h2; simp
  by_cases h3 : a = 3
  · subst h3; simp
  have : a ∉ m := fun ha => by
    have := hm a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at this; tauto
  rw [Multiset.count_eq_zero.2 this]
  simp [Ne.symm h1, Ne.symm h2, Ne.symm h3]

theorem A165640_ms_eq (n : ℕ) : A165640_ms n = A165640 n := by
  unfold A165640_ms A165640
  apply Finset.card_bij (fun (s : Sym ℤ n) _ => ((s : Multiset ℤ).count (-2), (s : Multiset ℤ).count 1,
    (s : Multiset ℤ).count 3))
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_sym_iff] at hs
    obtain ⟨hsupp, hsum⟩ := hs
    have hsupp' : ∀ a ∈ (s : Multiset ℤ), a ∈ ({-2, 1, 3} : Finset ℤ) := fun a ha => hsupp a ha
    have hd := A165640_decomp _ hsupp'
    have hcard : (s : Multiset ℤ).card = n := s.2
    rw [hd] at hcard hsum
    simp only [Multiset.card_add, Multiset.card_replicate, Multiset.sum_add,
      Multiset.sum_replicate, nsmul_eq_mul] at hcard hsum
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨by omega, by omega, by omega⟩, hcard, ?_⟩
    linarith
  · intro s hs t ht he
    simp only [Finset.mem_filter, Finset.mem_sym_iff] at hs ht
    simp only [Prod.mk.injEq] at he
    apply Sym.ext
    rw [A165640_decomp (s : Multiset ℤ) (fun a ha => hs.1 a ha),
      A165640_decomp (t : Multiset ℤ) (fun a ha => ht.1 a ha), he.1, he.2.1, he.2.2]
  · rintro ⟨x, y, z⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
    obtain ⟨-, hc, hs⟩ := h
    refine ⟨Sym.mk (Multiset.replicate x (-2) + Multiset.replicate y 1 + Multiset.replicate z 3) (by
      simp only [Multiset.card_add, Multiset.card_replicate]; omega), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_sym_iff]
      refine ⟨fun a ha => ?_, ?_⟩
      · have ha' : a ∈ Multiset.replicate x (-2) + Multiset.replicate y 1 +
            Multiset.replicate z 3 := (Sym.mem_mk _ _ _).1 ha
        simp only [Multiset.mem_add, Multiset.mem_replicate] at ha'
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases ha' with (⟨-, rfl⟩ | ⟨-, rfl⟩) | ⟨-, rfl⟩ <;> simp
      · show (Multiset.replicate x (-2) + Multiset.replicate y 1 + Multiset.replicate z 3).sum = 3
        simp only [Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul]
        linarith
    · show ((Multiset.replicate x (-2) + Multiset.replicate y 1 + Multiset.replicate z 3).count (-2),
        (Multiset.replicate x (-2) + Multiset.replicate y 1 + Multiset.replicate z 3).count 1,
        (Multiset.replicate x (-2) + Multiset.replicate y 1 + Multiset.replicate z 3).count 3) =
        (x, y, z)
      simp [Multiset.count_replicate]

/-- Main theorem in the multiset form of the OEIS definition. -/
theorem A165640_ms_main (n : ℕ) (hn : 1 ≤ n) :
    A165640_ms n = 4 * (n + 4) / 5 - 2 * (n + 4) / 3 := by
  rw [A165640_ms_eq, A165640_main n hn]
