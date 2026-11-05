/-
OEIS A165300, Mathlib proof of J. W. Layman's four rules.

Definition (name of the entry): a(n) is the smallest number not already present that
permits the cyclic repetition of the path 1, 2 of the digits in the sequence. Formally
(`A165300_adm`, `A165300_next`, `A165300_terms`, `A165300_a`): with prev = [a(1), ..., a(n-1)],
a(n) is the least m > 0 with m ∉ prev such that the concatenated decimal digits of
a(1), ..., a(n-1), m are 1, 2, 1, 2, ... (`A165300_W 0 L` is that word of length L).
`A165300_D m` is the list of decimal digits of m, most significant first.

Main theorems (x = digits of a(n), y = digits of a(n+1), n ≥ 1):
* `A165300_rule1`: n > 1, x begins and ends with 1 → y = x with the initial 1 deleted;
* `A165300_rule2`: x begins with 1 and ends with 2 → y = x ++ [1];
* `A165300_rule3`: x begins with 2 and ends with 1 → y = x ++ [2];
* `A165300_rule4`: x begins and ends with 2 → y = 1 :: x.
`A165300_closed`: a(1) = 1, a(2) = 2 and for j ≥ 0 a(4j+3), a(4j+4), a(4j+5), a(4j+6) are the
alternating numbers 1212...(2j+2 digits), 1212...1 (2j+3), 2121...(2j+2), 2121...2 (2j+3).
`A165300_data`: the 25 printed terms.

Proof: after a(4j+2) the used numbers are exactly the alternating numbers with at most
2j+1 digits starting with either digit, and the digit string has even length (2j+1)(2j+2).
The admissible m are exactly the alternating numbers starting with the next digit of the
pattern, ordered by length (`A165300_next_eq`), so the next term is the shortest unused one.

Not checked: nothing.
-/
import Mathlib

/-- The cyclic path 1, 2, 1, 2, ... -/
def A165300_pat (i : ℕ) : ℕ := if i % 2 = 0 then 1 else 2

/-- `W L l` = pat L, pat (L+1), ..., pat (L+l-1). -/
def A165300_W (L : ℕ) : ℕ → List ℕ
  | 0 => []
  | l + 1 => A165300_pat L :: A165300_W (L + 1) l

/-- Decimal digits, most significant first. -/
def A165300_D (m : ℕ) : List ℕ := (Nat.digits 10 m).reverse

/-- The concatenated digits of a list of numbers. -/
def A165300_cat (l : List ℕ) : List ℕ := l.flatMap A165300_D

/-- m may follow prev. -/
def A165300_adm (prev : List ℕ) (m : ℕ) : Prop :=
  0 < m ∧ m ∉ prev ∧
    A165300_cat (prev ++ [m]) = A165300_W 0 (A165300_cat (prev ++ [m])).length

open Classical in
/-- The least admissible m (0 if there is none; this never happens, see `A165300_next_eq`). -/
noncomputable def A165300_next (prev : List ℕ) : ℕ :=
  if h : ∃ m, A165300_adm prev m then Nat.find h else 0

/-- The first n terms. -/
noncomputable def A165300_terms : ℕ → List ℕ
  | 0 => []
  | n + 1 => A165300_terms n ++ [A165300_next (A165300_terms n)]

/-- a(n), n ≥ 1. -/
noncomputable def A165300_a (n : ℕ) : ℕ := A165300_next (A165300_terms (n - 1))

/-- The alternating number with l digits whose first digit is pat L. -/
def A165300_alt (L l : ℕ) : ℕ := Nat.ofDigits 10 (A165300_W L l).reverse

theorem A165300_pat_mod (i : ℕ) : A165300_pat i = A165300_pat (i % 2) := by
  unfold A165300_pat
  rw [Nat.mod_mod]

theorem A165300_pat_ne (i : ℕ) : A165300_pat i = 1 ∨ A165300_pat i = 2 := by
  unfold A165300_pat
  split_ifs <;> simp

theorem A165300_W_length (L l : ℕ) : (A165300_W L l).length = l := by
  induction l generalizing L with
  | zero => rfl
  | succ l ih => simp [A165300_W, ih]

theorem A165300_W_mem {L l x : ℕ} (h : x ∈ A165300_W L l) : x = 1 ∨ x = 2 := by
  induction l generalizing L with
  | zero => simp [A165300_W] at h
  | succ l ih =>
    simp only [A165300_W, List.mem_cons] at h
    rcases h with rfl | h
    · exact A165300_pat_ne L
    · exact ih h

theorem A165300_W_append (L a b : ℕ) :
    A165300_W L a ++ A165300_W (L + a) b = A165300_W L (a + b) := by
  induction a generalizing L with
  | zero => simp [A165300_W]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by ring]
    simp only [A165300_W, List.cons_append]
    rw [← ih (L + 1), show L + 1 + a = L + (a + 1) by ring]

theorem A165300_W_snoc (L l : ℕ) :
    A165300_W L (l + 1) = A165300_W L l ++ [A165300_pat (L + l)] := by
  rw [← A165300_W_append L l 1]
  simp [A165300_W]

theorem A165300_W_mod (L l : ℕ) : A165300_W L l = A165300_W (L % 2) l := by
  induction l generalizing L with
  | zero => rfl
  | succ l ih =>
    simp only [A165300_W]
    rw [A165300_pat_mod L, ih (L + 1), ih (L % 2 + 1),
      show (L % 2 + 1) % 2 = (L + 1) % 2 by omega]

theorem A165300_alt_mod (L l : ℕ) : A165300_alt L l = A165300_alt (L % 2) l := by
  unfold A165300_alt
  rw [A165300_W_mod]

theorem A165300_D_alt (L l : ℕ) : A165300_D (A165300_alt L l) = A165300_W L l := by
  unfold A165300_D A165300_alt
  rw [Nat.digits_ofDigits 10 (by norm_num), List.reverse_reverse]
  · intro x hx
    rcases A165300_W_mem (List.mem_reverse.mp hx) with rfl | rfl <;> norm_num
  · intro h
    rcases A165300_W_mem (List.mem_reverse.mp (List.getLast_mem h)) with h' | h' <;>
      rw [h'] <;> norm_num

theorem A165300_D_length (m : ℕ) : (A165300_D m).length = (Nat.digits 10 m).length := by
  simp [A165300_D]

theorem A165300_alt_pos {L l : ℕ} (hl : 1 ≤ l) : 0 < A165300_alt L l := by
  rcases Nat.eq_zero_or_pos (A165300_alt L l) with h | h
  · have := A165300_D_alt L l
    rw [h, A165300_D] at this
    have h2 := congrArg List.length this
    simp [A165300_W_length] at h2
    omega
  · exact h

theorem A165300_alt_digits_length (L l : ℕ) : (Nat.digits 10 (A165300_alt L l)).length = l := by
  rw [← A165300_D_length, A165300_D_alt, A165300_W_length]

theorem A165300_alt_lt {L L' l l' : ℕ} (hl : 1 ≤ l) (hll : l < l') :
    A165300_alt L l < A165300_alt L' l' := by
  have h1 := Nat.lt_base_pow_length_digits (b := 10) (m := A165300_alt L l) (by norm_num)
  have h2 := Nat.base_pow_length_digits_le 10 (A165300_alt L' l') (by norm_num)
    (A165300_alt_pos (by omega)).ne'
  rw [A165300_alt_digits_length] at h1 h2
  have h3 : 10 ^ (l + 1) ≤ 10 ^ l' := Nat.pow_le_pow_right (by norm_num) hll
  rw [pow_succ] at h3
  omega

theorem A165300_alt_inj {p p' l l' : ℕ} (hp : p < 2) (hp' : p' < 2) (hl : 1 ≤ l)
    (h : A165300_alt p l = A165300_alt p' l') : p = p' ∧ l = l' := by
  have hD := congrArg A165300_D h
  rw [A165300_D_alt, A165300_D_alt] at hD
  have hlen := congrArg List.length hD
  rw [A165300_W_length, A165300_W_length] at hlen
  subst hlen
  obtain ⟨l, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  simp only [A165300_W, List.cons.injEq] at hD
  have := hD.1
  unfold A165300_pat at this
  refine ⟨?_, rfl⟩
  split_ifs at this <;> omega

/-- A positive number whose digits continue the pattern from position L is alt L (length). -/
theorem A165300_eq_alt {m L : ℕ} (hm : 0 < m)
    (h : A165300_W 0 L ++ A165300_D m = A165300_W 0 (L + (A165300_D m).length)) :
    m = A165300_alt L (A165300_D m).length ∧ 1 ≤ (A165300_D m).length := by
  rw [← A165300_W_append 0 L, zero_add] at h
  have hD := List.append_cancel_left h
  refine ⟨?_, ?_⟩
  · unfold A165300_alt
    rw [← hD, A165300_D, List.reverse_reverse, Nat.ofDigits_digits]
  · rw [A165300_D_length]
    rcases Nat.exists_eq_succ_of_ne_zero hm.ne' with ⟨k, rfl⟩
    rw [Nat.digits_def' (by norm_num) (by omega)]
    simp

theorem A165300_cat_snoc (l : List ℕ) (m : ℕ) :
    A165300_cat (l ++ [m]) = A165300_cat l ++ A165300_D m := by
  simp [A165300_cat]

/-- The next term is the shortest alternating number, starting at phase L, not yet used. -/
theorem A165300_next_eq (prev : List ℕ) (L l : ℕ) (hc : A165300_cat prev = A165300_W 0 L)
    (hl : 1 ≤ l) (hnot : A165300_alt L l ∉ prev)
    (hmin : ∀ l', 1 ≤ l' → l' < l → A165300_alt L l' ∈ prev) :
    A165300_next prev = A165300_alt L l ∧
      A165300_cat (prev ++ [A165300_alt L l]) = A165300_W 0 (L + l) := by
  have hcat : A165300_cat (prev ++ [A165300_alt L l]) = A165300_W 0 (L + l) := by
    rw [A165300_cat_snoc, hc, A165300_D_alt, ← A165300_W_append 0 L l, zero_add]
  have hadm : A165300_adm prev (A165300_alt L l) :=
    ⟨A165300_alt_pos hl, hnot, by rw [hcat, A165300_W_length]⟩
  refine ⟨?_, hcat⟩
  classical
  have hex : ∃ m, A165300_adm prev m := ⟨_, hadm⟩
  unfold A165300_next
  split_ifs
  rw [Nat.find_eq_iff]
  refine ⟨hadm, ?_⟩
  rintro m hm ⟨hm0, hmp, hmc⟩
  rw [A165300_cat_snoc, hc, List.length_append, A165300_W_length] at hmc
  obtain ⟨heq, hk⟩ := A165300_eq_alt hm0 hmc
  set k := (A165300_D m).length
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · exact hmp (heq ▸ hmin k hk hkl)
  · rw [← heq] at hm
    exact lt_irrefl _ hm
  · have := A165300_alt_lt (L := L) (L' := L) hl hkl
    omega

theorem A165300_terms_succ (n : ℕ) :
    A165300_terms (n + 1) = A165300_terms n ++ [A165300_next (A165300_terms n)] := rfl

/-- State after 4j + 2 terms, and the next four terms. -/
theorem A165300_state (j : ℕ) :
    A165300_cat (A165300_terms (4 * j + 2)) = A165300_W 0 ((2 * j + 1) * (2 * j + 2)) ∧
    (∀ m, m ∈ A165300_terms (4 * j + 2) ↔
      ∃ p l, p < 2 ∧ 1 ≤ l ∧ l ≤ 2 * j + 1 ∧ m = A165300_alt p l) ∧
    A165300_next (A165300_terms (4 * j + 2)) = A165300_alt 0 (2 * j + 2) ∧
    A165300_next (A165300_terms (4 * j + 3)) = A165300_alt 0 (2 * j + 3) ∧
    A165300_next (A165300_terms (4 * j + 4)) = A165300_alt 1 (2 * j + 2) ∧
    A165300_next (A165300_terms (4 * j + 5)) = A165300_alt 1 (2 * j + 3) := by
  -- First the state claim alone, by induction; the four terms then follow from it.
  --
  have four : ∀ j, (A165300_cat (A165300_terms (4 * j + 2)) =
        A165300_W 0 ((2 * j + 1) * (2 * j + 2)) ∧
      (∀ m, m ∈ A165300_terms (4 * j + 2) ↔
        ∃ p l, p < 2 ∧ 1 ≤ l ∧ l ≤ 2 * j + 1 ∧ m = A165300_alt p l)) →
      A165300_next (A165300_terms (4 * j + 2)) = A165300_alt 0 (2 * j + 2) ∧
      A165300_next (A165300_terms (4 * j + 3)) = A165300_alt 0 (2 * j + 3) ∧
      A165300_next (A165300_terms (4 * j + 4)) = A165300_alt 1 (2 * j + 2) ∧
      A165300_next (A165300_terms (4 * j + 5)) = A165300_alt 1 (2 * j + 3) ∧
      A165300_cat (A165300_terms (4 * (j + 1) + 2)) =
        A165300_W 0 ((2 * (j + 1) + 1) * (2 * (j + 1) + 2)) ∧
      (∀ m, m ∈ A165300_terms (4 * (j + 1) + 2) ↔
        ∃ p l, p < 2 ∧ 1 ≤ l ∧ l ≤ 2 * (j + 1) + 1 ∧ m = A165300_alt p l) := by
    intro j ⟨hc, hm⟩
    obtain ⟨T, hT⟩ : ∃ T, (2 * j + 1) * (2 * j + 2) = 2 * T := ⟨(2 * j + 1) * (j + 1), by ring⟩
    rw [hT] at hc
    -- Step 1: phase 0, length 2j + 2.
    --
    have s1 := A165300_next_eq _ (2 * T) (2 * j + 2) hc (by omega)
      (by
        rw [hm]
        rintro ⟨p, l, hp, hl1, hl2, he⟩
        rw [A165300_alt_mod, show 2 * T % 2 = 0 by omega] at he
        have := A165300_alt_inj (by norm_num) hp (by omega) he
        omega)
      (by
        intro l' h1 h2
        rw [hm]
        exact ⟨0, l', by norm_num, h1, by omega, by rw [A165300_alt_mod]; congr 1; omega⟩)
    rw [A165300_alt_mod, show 2 * T % 2 = 0 by omega] at s1
    have e3 : A165300_terms (4 * j + 3) = A165300_terms (4 * j + 2) ++ [A165300_alt 0 (2 * j + 2)] := by
      rw [A165300_terms_succ, s1.1]
    have hm3 : ∀ m, m ∈ A165300_terms (4 * j + 3) ↔
        (∃ p l, p < 2 ∧ 1 ≤ l ∧ l ≤ 2 * j + 1 ∧ m = A165300_alt p l) ∨
          m = A165300_alt 0 (2 * j + 2) := by
      intro m
      rw [e3, List.mem_append, List.mem_singleton, hm]
    have hc3 : A165300_cat (A165300_terms (4 * j + 3)) = A165300_W 0 (2 * T + (2 * j + 2)) := by
      rw [e3, s1.2]
    -- Step 2: phase 0, length 2j + 3.
    --
    have s2 := A165300_next_eq _ (2 * T + (2 * j + 2)) (2 * j + 3) hc3 (by omega)
      (by
        rw [hm3, A165300_alt_mod, show (2 * T + (2 * j + 2)) % 2 = 0 by omega]
        rintro (⟨p, l, hp, hl1, hl2, he⟩ | he)
        · have := A165300_alt_inj (by norm_num) hp (by omega) he
          omega
        · have := A165300_alt_inj (by norm_num) (by norm_num) (by omega) he
          omega)
      (by
        intro l' h1 h2
        rw [hm3, A165300_alt_mod, show (2 * T + (2 * j + 2)) % 2 = 0 by omega]
        rcases Nat.lt_or_ge l' (2 * j + 2) with h | h
        · exact Or.inl ⟨0, l', by norm_num, h1, by omega, rfl⟩
        · exact Or.inr (by congr 1; omega))
    rw [A165300_alt_mod, show (2 * T + (2 * j + 2)) % 2 = 0 by omega] at s2
    have e4 : A165300_terms (4 * j + 4) = A165300_terms (4 * j + 3) ++ [A165300_alt 0 (2 * j + 3)] := by
      rw [A165300_terms_succ, s2.1]
    have hm4 : ∀ m, m ∈ A165300_terms (4 * j + 4) ↔
        (∃ p l, p < 2 ∧ 1 ≤ l ∧ l ≤ 2 * j + 1 ∧ m = A165300_alt p l) ∨
          m = A165300_alt 0 (2 * j + 2) ∨ m = A165300_alt 0 (2 * j + 3) := by
      intro m
      rw [e4, List.mem_append, List.mem_singleton, hm3, or_assoc]
    have hc4 : A165300_cat (A165300_terms (4 * j + 4)) =
        A165300_W 0 (2 * T + (2 * j + 2) + (2 * j + 3)) := by
      rw [e4, s2.2]
    -- Step 3: phase 1, length 2j + 2.
    --
    have hpar3 : (2 * T + (2 * j + 2) + (2 * j + 3)) % 2 = 1 := by omega
    have s3 := A165300_next_eq _ (2 * T + (2 * j + 2) + (2 * j + 3)) (2 * j + 2) hc4 (by omega)
      (by
        rw [hm4, A165300_alt_mod, hpar3]
        rintro (⟨p, l, hp, hl1, hl2, he⟩ | he | he)
        · have := A165300_alt_inj (by norm_num) hp (by omega) he
          omega
        · have := A165300_alt_inj (by norm_num) (by norm_num) (by omega) he
          omega
        · have := A165300_alt_inj (by norm_num) (by norm_num) (by omega) he
          omega)
      (by
        intro l' h1 h2
        rw [hm4, A165300_alt_mod, hpar3]
        exact Or.inl ⟨1, l', by norm_num, h1, by omega, rfl⟩)
    rw [A165300_alt_mod, hpar3] at s3
    have e5 : A165300_terms (4 * j + 5) = A165300_terms (4 * j + 4) ++ [A165300_alt 1 (2 * j + 2)] := by
      rw [A165300_terms_succ, s3.1]
    have hm5 : ∀ m, m ∈ A165300_terms (4 * j + 5) ↔
        (∃ p l, p < 2 ∧ 1 ≤ l ∧ l ≤ 2 * j + 1 ∧ m = A165300_alt p l) ∨
          m = A165300_alt 0 (2 * j + 2) ∨ m = A165300_alt 0 (2 * j + 3) ∨
          m = A165300_alt 1 (2 * j + 2) := by
      intro m
      rw [e5, List.mem_append, List.mem_singleton, hm4, or_assoc, or_assoc]
    have hc5 : A165300_cat (A165300_terms (4 * j + 5)) =
        A165300_W 0 (2 * T + (2 * j + 2) + (2 * j + 3) + (2 * j + 2)) := by
      rw [e5, s3.2]
    -- Step 4: phase 1, length 2j + 3.
    --
    have hpar4 : (2 * T + (2 * j + 2) + (2 * j + 3) + (2 * j + 2)) % 2 = 1 := by omega
    have s4 := A165300_next_eq _ _ (2 * j + 3) hc5 (by omega)
      (by
        rw [hm5, A165300_alt_mod, hpar4]
        rintro (⟨p, l, hp, hl1, hl2, he⟩ | he | he | he)
        · have := A165300_alt_inj (by norm_num) hp (by omega) he
          omega
        · have := A165300_alt_inj (by norm_num) (by norm_num) (by omega) he
          omega
        · have := A165300_alt_inj (by norm_num) (by norm_num) (by omega) he
          omega
        · have := A165300_alt_inj (by norm_num) (by norm_num) (by omega) he
          omega)
      (by
        intro l' h1 h2
        rw [hm5, A165300_alt_mod, hpar4]
        rcases Nat.lt_or_ge l' (2 * j + 2) with h | h
        · exact Or.inl ⟨1, l', by norm_num, h1, by omega, rfl⟩
        · exact Or.inr (Or.inr (Or.inr (by congr 1; omega))))
    rw [A165300_alt_mod, hpar4] at s4
    have e6 : A165300_terms (4 * (j + 1) + 2) =
        A165300_terms (4 * j + 5) ++ [A165300_alt 1 (2 * j + 3)] := by
      rw [show 4 * (j + 1) + 2 = 4 * j + 5 + 1 by ring, A165300_terms_succ, s4.1]
    refine ⟨s1.1, s2.1, s3.1, s4.1, ?_, ?_⟩
    · rw [e6, s4.2]
      congr 1
      nlinarith
    · intro m
      rw [e6, List.mem_append, List.mem_singleton, hm5]
      constructor
      · rintro ((⟨p, l, hp, hl1, hl2, he⟩ | he | he | he) | he)
        · exact ⟨p, l, hp, hl1, by omega, he⟩
        · exact ⟨0, 2 * j + 2, by norm_num, by omega, by omega, he⟩
        · exact ⟨0, 2 * j + 3, by norm_num, by omega, by omega, he⟩
        · exact ⟨1, 2 * j + 2, by norm_num, by omega, by omega, he⟩
        · exact ⟨1, 2 * j + 3, by norm_num, by omega, by omega, he⟩
      · rintro ⟨p, l, hp, hl1, hl2, he⟩
        rcases Nat.lt_or_ge l (2 * j + 2) with h | h
        · exact Or.inl (Or.inl ⟨p, l, hp, hl1, by omega, he⟩)
        · obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
          · obtain rfl | rfl : l = 2 * j + 2 ∨ l = 2 * j + 3 := by omega
            · exact Or.inl (Or.inr (Or.inl he))
            · exact Or.inl (Or.inr (Or.inr (Or.inl he)))
          · obtain rfl | rfl : l = 2 * j + 2 ∨ l = 2 * j + 3 := by omega
            · exact Or.inl (Or.inr (Or.inr (Or.inr he)))
            · exact Or.inr he
  -- Base: terms 2 = [1, 2].
  --
  have base : A165300_cat (A165300_terms (4 * 0 + 2)) = A165300_W 0 ((2 * 0 + 1) * (2 * 0 + 2)) ∧
      (∀ m, m ∈ A165300_terms (4 * 0 + 2) ↔
        ∃ p l, p < 2 ∧ 1 ≤ l ∧ l ≤ 2 * 0 + 1 ∧ m = A165300_alt p l) := by
    have t1 := A165300_next_eq [] 0 1 (by simp [A165300_cat, A165300_W]) le_rfl (by simp)
      (by intro l' h1 h2; omega)
    have e1 : A165300_terms 1 = [A165300_alt 0 1] := by
      rw [A165300_terms_succ, show A165300_terms 0 = [] from rfl, t1.1]
      rfl
    have t2 := A165300_next_eq [A165300_alt 0 1] 1 1 (by rw [← e1]; rw [e1]; exact t1.2) le_rfl
      (by
        rw [List.mem_singleton]
        intro he
        have := A165300_alt_inj (by norm_num) (by norm_num) le_rfl he
        omega)
      (by intro l' h1 h2; omega)
    have e2 : A165300_terms 2 = [A165300_alt 0 1, A165300_alt 1 1] := by
      rw [A165300_terms_succ, e1, t2.1]
      rfl
    refine ⟨?_, ?_⟩
    · rw [show 4 * 0 + 2 = 2 by rfl, e2]
      exact t2.2
    · intro m
      rw [show 4 * 0 + 2 = 2 by rfl, e2]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨0, 1, by norm_num, le_rfl, le_rfl, rfl⟩
        · exact ⟨1, 1, by norm_num, le_rfl, le_rfl, rfl⟩
      · rintro ⟨p, l, hp, hl1, hl2, rfl⟩
        obtain rfl : l = 1 := by omega
        obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
        · exact Or.inl rfl
        · exact Or.inr rfl
  have st : ∀ j, A165300_cat (A165300_terms (4 * j + 2)) =
        A165300_W 0 ((2 * j + 1) * (2 * j + 2)) ∧
      (∀ m, m ∈ A165300_terms (4 * j + 2) ↔
        ∃ p l, p < 2 ∧ 1 ≤ l ∧ l ≤ 2 * j + 1 ∧ m = A165300_alt p l) := by
    intro j
    induction j with
    | zero => exact base
    | succ j ih => exact ⟨(four j ih).2.2.2.2.1, (four j ih).2.2.2.2.2⟩
  exact ⟨(st j).1, (st j).2, (four j (st j)).1, (four j (st j)).2.1, (four j (st j)).2.2.1,
    (four j (st j)).2.2.2.1⟩

/-- Closed form of a(n): a(1) = 1, a(2) = 2 and the four residues mod 4 from n = 3. -/
def A165300_cf (n : ℕ) : ℕ :=
  if n ≤ 2 then n
  else A165300_alt (if (n - 3) % 4 < 2 then 0 else 1) (2 * ((n - 3) / 4) + 2 + (n - 3) % 2)

theorem A165300_cf0 (j : ℕ) : A165300_cf (4 * j + 3) = A165300_alt 0 (2 * j + 2) := by
  unfold A165300_cf
  rw [ite_eq_right (by omega), show 4 * j + 3 - 3 = 4 * j by omega,
    show 4 * j % 4 = 0 by omega, show 4 * j / 4 = j by omega, show 4 * j % 2 = 0 by omega]
  rfl

theorem A165300_cf1 (j : ℕ) : A165300_cf (4 * j + 4) = A165300_alt 0 (2 * j + 3) := by
  unfold A165300_cf
  rw [ite_eq_right (by omega), show 4 * j + 4 - 3 = 4 * j + 1 by omega,
    show (4 * j + 1) % 4 = 1 by omega, show (4 * j + 1) / 4 = j by omega,
    show (4 * j + 1) % 2 = 1 by omega]
  rfl

theorem A165300_cf2 (j : ℕ) : A165300_cf (4 * j + 5) = A165300_alt 1 (2 * j + 2) := by
  unfold A165300_cf
  rw [ite_eq_right (by omega), show 4 * j + 5 - 3 = 4 * j + 2 by omega,
    show (4 * j + 2) % 4 = 2 by omega, show (4 * j + 2) / 4 = j by omega,
    show (4 * j + 2) % 2 = 0 by omega]
  rfl

theorem A165300_cf3 (j : ℕ) : A165300_cf (4 * j + 6) = A165300_alt 1 (2 * j + 3) := by
  unfold A165300_cf
  rw [ite_eq_right (by omega), show 4 * j + 6 - 3 = 4 * j + 3 by omega,
    show (4 * j + 3) % 4 = 3 by omega, show (4 * j + 3) / 4 = j by omega,
    show (4 * j + 3) % 2 = 1 by omega]
  rfl

theorem A165300_closed (n : ℕ) (hn : 1 ≤ n) : A165300_a n = A165300_cf n := by
  have h12 : A165300_terms 2 = [1, 2] := by
    have t1 := A165300_next_eq [] 0 1 (by simp [A165300_cat, A165300_W]) le_rfl (by simp)
      (by intro l' h1 h2; omega)
    have e1 : A165300_terms 1 = [1] := by
      rw [A165300_terms_succ, show A165300_terms 0 = [] from rfl, t1.1]
      rfl
    have t2 := A165300_next_eq [1] 1 1 (by rw [← e1]; rw [e1]; exact t1.2) le_rfl
      (by decide) (by intro l' h1 h2; omega)
    rw [A165300_terms_succ, e1, t2.1]
    rfl
  rcases Nat.lt_or_ge n 3 with h | h
  · unfold A165300_a A165300_cf
    rw [ite_eq_left (by omega)]
    obtain rfl | rfl : n = 1 ∨ n = 2 := by omega
    · have : A165300_terms 1 = [A165300_next (A165300_terms 0)] := rfl
      have h1 := congrArg List.head? h12
      rw [show (2 : ℕ) = 1 + 1 from rfl, A165300_terms_succ, this] at h1
      simpa using h1
    · have h1 := congrArg List.getLast? h12
      rw [show (2 : ℕ) = 1 + 1 from rfl, A165300_terms_succ] at h1
      simpa using h1
  · obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 4 ∧ n = 4 * j + 3 + r :=
      ⟨(n - 3) / 4, (n - 3) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
    have S := A165300_state j
    unfold A165300_a
    obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    · rw [show 4 * j + 3 + 0 - 1 = 4 * j + 2 by omega, S.2.2.1,
        show 4 * j + 3 + 0 = 4 * j + 3 by omega, A165300_cf0]
    · rw [show 4 * j + 3 + 1 - 1 = 4 * j + 3 by omega, S.2.2.2.1,
        show 4 * j + 3 + 1 = 4 * j + 4 by omega, A165300_cf1]
    · rw [show 4 * j + 3 + 2 - 1 = 4 * j + 4 by omega, S.2.2.2.2.1,
        show 4 * j + 3 + 2 = 4 * j + 5 by omega, A165300_cf2]
    · rw [show 4 * j + 3 + 3 - 1 = 4 * j + 5 by omega, S.2.2.2.2.2,
        show 4 * j + 3 + 3 = 4 * j + 6 by omega, A165300_cf3]

theorem A165300_data :
    (List.range 25).map (fun i => A165300_a (i + 1)) =
      [1,2,12,121,21,212,1212,12121,2121,21212,121212,1212121,212121,
       2121212,12121212,121212121,21212121,212121212,1212121212,12121212121,
       2121212121,21212121212,121212121212,1212121212121,212121212121] := by
  rw [List.map_congr_left (g := fun i => A165300_cf (i + 1))
    (fun i _ => A165300_closed (i + 1) (by omega))]
  decide

/-- Digits of a(n) and a(n+1) for n ≥ 2: four shapes. -/
theorem A165300_shape (n : ℕ) (hn : 2 ≤ n) :
    (∃ j, A165300_D (A165300_a n) = A165300_W 0 (2 * j + 2) ∧
      A165300_D (A165300_a (n + 1)) = A165300_W 0 (2 * j + 3)) ∨
    (∃ j, A165300_D (A165300_a n) = A165300_W 0 (2 * j + 3) ∧
      A165300_D (A165300_a (n + 1)) = A165300_W 1 (2 * j + 2)) ∨
    (∃ j, A165300_D (A165300_a n) = A165300_W 1 (2 * j + 2) ∧
      A165300_D (A165300_a (n + 1)) = A165300_W 1 (2 * j + 3)) ∨
    (∃ j, A165300_D (A165300_a n) = A165300_W 1 (2 * j + 1) ∧
      A165300_D (A165300_a (n + 1)) = A165300_W 0 (2 * j + 2)) := by
  rw [A165300_closed n (by omega), A165300_closed (n + 1) (by omega)]
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    refine Or.inr (Or.inr (Or.inr ⟨0, ?_, ?_⟩))
    · rw [show A165300_cf 2 = A165300_alt 1 1 by decide, A165300_D_alt]
    · rw [show 2 + 1 = 4 * 0 + 3 by rfl, A165300_cf0, A165300_D_alt]
  · obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 4 ∧ n = 4 * j + 3 + r :=
      ⟨(n - 3) / 4, (n - 3) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
    obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    · refine Or.inl ⟨j, ?_, ?_⟩
      · rw [show 4 * j + 3 + 0 = 4 * j + 3 by omega, A165300_cf0, A165300_D_alt]
      · rw [show 4 * j + 3 + 0 + 1 = 4 * j + 4 by omega, A165300_cf1, A165300_D_alt]
    · refine Or.inr (Or.inl ⟨j, ?_, ?_⟩)
      · rw [show 4 * j + 3 + 1 = 4 * j + 4 by omega, A165300_cf1, A165300_D_alt]
      · rw [show 4 * j + 3 + 1 + 1 = 4 * j + 5 by omega, A165300_cf2, A165300_D_alt]
    · refine Or.inr (Or.inr (Or.inl ⟨j, ?_, ?_⟩))
      · rw [show 4 * j + 3 + 2 = 4 * j + 5 by omega, A165300_cf2, A165300_D_alt]
      · rw [show 4 * j + 3 + 2 + 1 = 4 * j + 6 by omega, A165300_cf3, A165300_D_alt]
    · refine Or.inr (Or.inr (Or.inr ⟨j + 1, ?_, ?_⟩))
      · rw [show 4 * j + 3 + 3 = 4 * j + 6 by omega, A165300_cf3, A165300_D_alt,
          show 2 * (j + 1) + 1 = 2 * j + 3 by ring]
      · rw [show 4 * j + 3 + 3 + 1 = 4 * (j + 1) + 3 by ring, A165300_cf0, A165300_D_alt]

theorem A165300_head (L l : ℕ) : (A165300_W L (l + 1)).head? = some (A165300_pat L) := by
  simp [A165300_W]

theorem A165300_last (L l : ℕ) :
    (A165300_W L (l + 1)).getLast? = some (A165300_pat (L + l)) := by
  rw [A165300_W_snoc]
  simp

theorem A165300_pat_eval (i : ℕ) : A165300_pat i = if i % 2 = 0 then 1 else 2 := rfl

/-- The four-way case data, with first and last digits evaluated. -/
theorem A165300_cases (n : ℕ) (hn : 2 ≤ n) :
    let x := A165300_D (A165300_a n)
    let y := A165300_D (A165300_a (n + 1))
    (x.head? = some 1 ∧ x.getLast? = some 2 ∧ y = x ++ [1]) ∨
    (x.head? = some 1 ∧ x.getLast? = some 1 ∧ y = x.tail) ∨
    (x.head? = some 2 ∧ x.getLast? = some 1 ∧ y = x ++ [2]) ∨
    (x.head? = some 2 ∧ x.getLast? = some 2 ∧ y = 1 :: x) := by
  intro x y
  rcases A165300_shape n hn with ⟨j, hx, hy⟩ | ⟨j, hx, hy⟩ | ⟨j, hx, hy⟩ | ⟨j, hx, hy⟩ <;>
    simp only [x, y, hx, hy]
  · refine Or.inl ⟨by rw [A165300_head]; rfl, ?_, ?_⟩
    · rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, A165300_last, A165300_pat_eval,
        ite_eq_right (by omega)]
    · rw [show 2 * j + 3 = (2 * j + 2) + 1 by ring, A165300_W_snoc, A165300_pat_eval,
        ite_eq_left (by omega)]
  · refine Or.inr (Or.inl ⟨by rw [A165300_head]; rfl, ?_, ?_⟩)
    · rw [show 2 * j + 3 = (2 * j + 2) + 1 by ring, A165300_last, A165300_pat_eval,
        ite_eq_left (by omega)]
    · rw [show 2 * j + 3 = (2 * j + 2) + 1 by ring, A165300_W]
      rfl
  · refine Or.inr (Or.inr (Or.inl ⟨by rw [A165300_head]; rfl, ?_, ?_⟩))
    · rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, A165300_last, A165300_pat_eval,
        ite_eq_left (by omega)]
    · rw [show 2 * j + 3 = (2 * j + 2) + 1 by ring, A165300_W_snoc, A165300_pat_eval,
        ite_eq_right (by omega)]
  · refine Or.inr (Or.inr (Or.inr ⟨by rw [A165300_head]; rfl, ?_, ?_⟩))
    · rw [show 2 * j + 1 = (2 * j) + 1 by ring, A165300_last, A165300_pat_eval,
        ite_eq_right (by omega)]
    · rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, A165300_W]
      rfl

theorem A165300_rule1 (n : ℕ) (hn : 1 < n)
    (h1 : (A165300_D (A165300_a n)).head? = some 1)
    (h2 : (A165300_D (A165300_a n)).getLast? = some 1) :
    A165300_D (A165300_a (n + 1)) = (A165300_D (A165300_a n)).tail := by
  rcases A165300_cases n hn with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;>
    simp_all

theorem A165300_a_one : A165300_a 1 = 1 := (A165300_closed 1 le_rfl).trans (by decide)

theorem A165300_rule2 (n : ℕ) (hn : 1 ≤ n)
    (h1 : (A165300_D (A165300_a n)).head? = some 1)
    (h2 : (A165300_D (A165300_a n)).getLast? = some 2) :
    A165300_D (A165300_a (n + 1)) = A165300_D (A165300_a n) ++ [1] := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [A165300_a_one] at h2
    simp [A165300_D] at h2
  · rcases A165300_cases n h with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;>
      simp_all

theorem A165300_rule3 (n : ℕ) (hn : 1 ≤ n)
    (h1 : (A165300_D (A165300_a n)).head? = some 2)
    (h2 : (A165300_D (A165300_a n)).getLast? = some 1) :
    A165300_D (A165300_a (n + 1)) = A165300_D (A165300_a n) ++ [2] := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [A165300_a_one] at h1
    simp [A165300_D] at h1
  · rcases A165300_cases n h with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;>
      simp_all

theorem A165300_rule4 (n : ℕ) (hn : 1 ≤ n)
    (h1 : (A165300_D (A165300_a n)).head? = some 2)
    (h2 : (A165300_D (A165300_a n)).getLast? = some 2) :
    A165300_D (A165300_a (n + 1)) = 1 :: A165300_D (A165300_a n) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [A165300_a_one] at h1
    simp [A165300_D] at h1
  · rcases A165300_cases n h with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;>
      simp_all
