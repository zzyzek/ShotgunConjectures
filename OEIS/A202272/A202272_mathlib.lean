/-
OEIS A202272: numbers n such that every sum of 1, 2, ..., k of the k digits of n is a substring
of n. Conjecture in the entry: the terms are exactly k*10^j, 10X (X: one 9, rest 0, length >= 1)
and 9Y10Z (Y, Z strings of 0s).

Proved here (`A202272_main`): `IsTerm n` iff n has at most one nonzero digit, or its nonzero
digits are exactly one 1 and one 9 and the block "10" occurs in n. `IsTerm` quantifies over all
sublists of the digit list (= all choices of digit positions) and asks that the digit list of the
sum be an infix; lists are least-significant-digit first (Mathlib `Nat.digits`), and an infix of a
reversed list is a reversed infix, so this is the substring condition. A sum 0 (only zero digits
chosen) has digit list [] here; in the decimal reading "0" must occur, which it does whenever a
zero digit was chosen, so the two readings agree.

Route: `one_mem_digits` (two nonzero digits force a digit 1, via a partial sum in [10, 18]);
`no_two_ones` (two 1s force all digits 1..9 (`all_mem`), then every value up to the digit sum is
a block (`cover`), and counting blocks by leading digit (`card_infSet`, `block_count`) makes the
digit sum exceed every power of 10); `no_mid`, `no_two_nines` (one 1: the sums 17, 15, 11 and 18
exclude the digits 2..8 and a second 9); `forward`, `backward`.

Not in Lean: the translation of the characterization into the entry's three explicit forms
(at most one nonzero digit is k*10^j; nonzero digits {1, 9} with "10" present is 10X or 9Y10Z
according to whether the leading digit is 1 or 9).
-/
import Mathlib

open List

-- `D n`: decimal digits of `n`, least significant first (Mathlib `Nat.digits`).
notation "D" => Nat.digits 10

/-- n is a term of A202272: for every nonempty choice of digit positions, the decimal string of
the sum of the chosen digits occurs as a block of consecutive digits of n. (Both strings are read
least significant digit first; a block of the reversed string is a reversed block.) -/
def IsTerm (n : ℕ) : Prop :=
  ∀ l : List ℕ, l <+ D n → l ≠ [] → D l.sum <:+: D n

lemma term_subperm {n : ℕ} (h : IsTerm n) {s : List ℕ} (hs : s <+~ D n) (hne : s ≠ []) :
    D s.sum <:+: D n := by
  obtain ⟨l, hp, hl⟩ := hs
  have hl0 : l ≠ [] := by
    intro h0; subst h0; exact hne (List.Perm.nil_eq hp).symm
  have := h l hl hl0
  rwa [hp.sum_eq] at this

lemma subperm_pair {L : List ℕ} {a b : ℕ} (hab : a ≠ b) (ha : a ∈ L) (hb : b ∈ L) :
    [a, b] <+~ L := by
  rw [List.subperm_ext_iff]
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · simpa [hab] using ha
  · simpa [hab, Ne.symm hab] using hb

lemma subperm_same {L : List ℕ} {a : ℕ} (h : 2 ≤ L.count a) : [a, a] <+~ L := by
  rw [List.subperm_ext_iff]
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
  subst hx
  simpa using h

lemma digits_single {d : ℕ} (h1 : 1 ≤ d) (h9 : d ≤ 9) : D d = [d] := by
  interval_cases d <;> simp

lemma mem_of_infix {a : ℕ} {L M : List ℕ} (h : L <:+: M) (ha : a ∈ L) : a ∈ M := h.subset ha

/-- one-digit sums: if the digit d (1..9) is a sub-multiset sum, d is a digit. -/
lemma digit_of_sum {n : ℕ} (h : IsTerm n) {s : List ℕ} (hs : s <+~ D n) (h1 : 1 ≤ s.sum)
    (h9 : s.sum ≤ 9) : s.sum ∈ D n := by
  have hne : s ≠ [] := by rintro rfl; simp at h1
  have := term_subperm h hs hne
  rw [digits_single h1 h9] at this
  exact mem_of_infix this (by simp)

/-- Partial sums of a list of numbers at most 9 hit every window [T, T + 8] below the total. -/
lemma prefix_window : ∀ (l : List ℕ), (∀ x ∈ l, x ≤ 9) → ∀ T, T ≤ l.sum →
    ∃ k, T ≤ (l.take k).sum ∧ (l.take k).sum ≤ T + 8
  | [], _, T, hT => ⟨0, by simpa using hT, by simp⟩
  | a :: t, hl, T, hT => by
    have ha : a ≤ 9 := hl a (by simp)
    by_cases h0 : T = 0
    · exact ⟨0, by simp [h0], by simp⟩
    by_cases hTa : T ≤ a
    · exact ⟨1, by simpa using hTa, by simp; omega⟩
    · have hT' : T - a ≤ t.sum := by simp at hT; omega
      obtain ⟨k, hk1, hk2⟩ := prefix_window t (fun x hx => hl x (by simp [hx])) (T - a) hT'
      exact ⟨k + 1, by simp; omega, by simp; omega⟩

/-- The nonzero digits of n. -/
abbrev NZ (n : ℕ) : List ℕ := (D n).filter (fun x => x ≠ 0)

lemma nz_sublist (n : ℕ) : NZ n <+ D n := List.filter_sublist

lemma nz_le9 {n x : ℕ} (hx : x ∈ NZ n) : x ≤ 9 := by
  have := Nat.digits_lt_base (b := 10) (by norm_num) (List.mem_filter.mp hx).1
  omega

lemma nz_pos {n x : ℕ} (hx : x ∈ NZ n) : 1 ≤ x := by
  have := (List.mem_filter.mp hx).2
  simp at this; omega

lemma count_nz {n a : ℕ} (ha : a ≠ 0) : (NZ n).count a = (D n).count a := by
  simp [NZ, List.count_filter, ha]

lemma mem_nz {n a : ℕ} (ha : a ≠ 0) (h : a ∈ D n) : a ∈ NZ n := List.mem_filter.mpr ⟨h, by simpa⟩

lemma sum_ge_length {l : List ℕ} (h : ∀ x ∈ l, 1 ≤ x) : l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have := h a (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    simp; omega

lemma sum_ge_ten {n : ℕ} (h : IsTerm n) (hM : 2 ≤ (NZ n).length) : 10 ≤ (NZ n).sum := by
  by_contra hlt
  replace hlt := Nat.lt_of_not_le hlt
  have hlen := sum_ge_length (l := NZ n) (fun x hx => nz_pos hx)
  have hS := digit_of_sum h (nz_sublist n).subperm (by omega) (by omega)
  have hSM : (NZ n).sum ∈ NZ n := List.mem_filter.mpr ⟨hS, by simp; omega⟩
  have hp := List.perm_cons_erase hSM
  have hsum := hp.sum_eq
  have hlen2 := hp.length_eq
  have hrest := sum_ge_length (l := (NZ n).erase (NZ n).sum)
    (fun x hx => nz_pos (List.mem_of_mem_erase hx))
  simp at hsum hlen2
  omega

lemma digits_teens {v : ℕ} (h1 : 10 ≤ v) (h2 : v ≤ 18) : 1 ∈ D v := by
  interval_cases v <;> simp

lemma one_mem_digits {n : ℕ} (h : IsTerm n) (hM : 2 ≤ (NZ n).length) : 1 ∈ D n := by
  obtain ⟨k, hk1, hk2⟩ := prefix_window (NZ n) (fun x hx => nz_le9 hx) 10 (sum_ge_ten h hM)
  have hsub : (NZ n).take k <+ D n := (List.take_sublist k _).trans (nz_sublist n)
  have hne : (NZ n).take k ≠ [] := by
    intro h0; rw [h0] at hk1; simp at hk1
  exact mem_of_infix (h _ hsub hne) (digits_teens hk1 hk2)

lemma succ_mem {n d : ℕ} (h : IsTerm n) (h1 : 1 ∈ D n) (hd2 : 2 ≤ d) (hd8 : d ≤ 8)
    (hd : d ∈ D n) : d + 1 ∈ D n := by
  have := digit_of_sum h (subperm_pair (a := 1) (b := d) (by omega) h1 hd) (by simp) (by simp; omega)
  simpa [add_comm] using this

lemma up_closed {n d : ℕ} (h : IsTerm n) (h1 : 1 ∈ D n) (hd2 : 2 ≤ d) (hd : d ∈ D n) :
    ∀ e, d ≤ e → e ≤ 9 → e ∈ D n := by
  intro e hde he9
  induction e, hde using Nat.le_induction with
  | base => exact hd
  | succ e hde ih => exact succ_mem h h1 (by omega) (by omega) (ih (by omega))

lemma count_of_infix {a : ℕ} {L M : List ℕ} (h : L <:+: M) : L.count a ≤ M.count a :=
  h.sublist.count_le a

lemma all_mem {n : ℕ} (h : IsTerm n) (hc : 2 ≤ (D n).count 1) :
    ∀ d, 1 ≤ d → d ≤ 9 → d ∈ D n := by
  have h1 : 1 ∈ D n := List.count_pos_iff.mp (by omega)
  have h2 : 2 ∈ D n := by
    simpa using digit_of_sum h (subperm_same hc) (by simp) (by simp)
  intro d hd1 hd9
  rcases Nat.lt_or_ge d 2 with hlt | hge
  · obtain rfl : d = 1 := by omega
    exact h1
  · exact up_closed h h1 (le_refl 2) h2 d hge hd9

lemma no_mid {n : ℕ} (h : IsTerm n) (hc1 : (D n).count 1 = 1) :
    ∀ d, 2 ≤ d → d ≤ 8 → d ∉ D n := by
  have h1 : 1 ∈ D n := List.count_pos_iff.mp (by omega)
  intro d hd2 hd8 hd
  have h8 := up_closed h h1 hd2 hd 8 hd8 (by norm_num)
  have h9 := up_closed h h1 hd2 hd 9 (by omega) (by norm_num)
  have h17 := term_subperm h (subperm_pair (a := 8) (b := 9) (by norm_num) h8 h9) (by simp)
  have h7 : 7 ∈ D n := mem_of_infix h17 (by norm_num)
  have h8' := up_closed h h1 (by norm_num) h7 8 (by norm_num) (by norm_num)
  have h15 := term_subperm h (subperm_pair (a := 7) (b := 8) (by norm_num) h7 h8') (by simp)
  have h5 : 5 ∈ D n := mem_of_infix h15 (by norm_num)
  have h6 := up_closed h h1 (by norm_num) h5 6 (by norm_num) (by norm_num)
  have h11 := term_subperm h (subperm_pair (a := 5) (b := 6) (by norm_num) h5 h6) (by simp)
  have := count_of_infix (a := 1) h11
  norm_num at this
  omega

lemma no_two_nines {n : ℕ} (h : IsTerm n) (hc1 : (D n).count 1 = 1) : (D n).count 9 ≤ 1 := by
  by_contra hc
  have h18 := term_subperm h (subperm_same (a := 9) (by omega)) (by simp)
  have h8 : 8 ∈ D n := mem_of_infix h18 (by norm_num)
  exact no_mid h hc1 8 (by norm_num) (by norm_num) h8

/-- Infixes of `L` of length `m` whose last entry is `c`. -/
def infSet (L : List ℕ) (m c : ℕ) : Finset (List ℕ) :=
  ((L.tails.flatMap List.inits).toFinset).filter (fun x => x.length = m ∧ x.getLast? = some c)

lemma mem_infSet {L x : List ℕ} {m c : ℕ} :
    x ∈ infSet L m c ↔ x <:+: L ∧ x.length = m ∧ x.getLast? = some c := by
  have key : x ∈ L.tails.flatMap List.inits ↔ x <:+: L := by
    rw [List.mem_flatMap, List.infix_iff_prefix_suffix]
    constructor
    · rintro ⟨t, ht, hx⟩
      exact ⟨t, (List.mem_inits _ _).mp hx, (List.mem_tails _ _).mp ht⟩
    · rintro ⟨t, hx, ht⟩
      exact ⟨t, (List.mem_tails _ _).mpr ht, (List.mem_inits _ _).mpr hx⟩
  simp only [infSet, Finset.mem_filter, List.mem_toFinset, key]

lemma getLast_of_suffix {x L : List ℕ} {b : ℕ} (h : x <:+ L ++ [b]) (hx : x ≠ []) :
    x.getLast? = some b := by
  obtain ⟨s, hs⟩ := h
  have h1 : (s ++ x).getLast? = x.getLast? := List.getLast?_append_of_ne_nil s hx
  rw [hs] at h1
  simpa using h1.symm

/-- At most `count c L` infixes of length `m ≥ 1` end in `c` (one per position holding `c`). -/
lemma card_infSet (c m : ℕ) (hm : 1 ≤ m) (L : List ℕ) : (infSet L m c).card ≤ L.count c := by
  induction L using List.reverseRecOn with
  | nil =>
    have : infSet [] m c = ∅ := by
      ext x
      simp only [mem_infSet, Finset.notMem_empty, iff_false, not_and]
      intro hx hl
      have := hx.length_le
      simp only [List.length_nil] at this; omega
    simp [this]
  | append_singleton L' b ih =>
    have hsub : infSet (L' ++ [b]) m c ⊆ infSet L' m c ∪
        ({(L' ++ [b]).drop ((L' ++ [b]).length - m)} : Finset (List ℕ)).filter (fun _ => b = c) := by
      intro x hx
      rw [mem_infSet] at hx
      obtain ⟨hinf, hlen, hlast⟩ := hx
      rcases List.infix_concat_iff.mp hinf with hsuf | hinf'
      · apply Finset.mem_union_right
        have hxne : x ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen; omega
        have hb := getLast_of_suffix hsuf hxne
        rw [hlast] at hb
        have hbc : b = c := (Option.some.inj hb).symm
        have hxd : x = (L' ++ [b]).drop ((L' ++ [b]).length - m) := by
          rw [← hlen]; exact List.suffix_iff_eq_drop.mp hsuf
        simp [hxd, hbc]
      · apply Finset.mem_union_left
        rw [mem_infSet]; exact ⟨hinf', hlen, hlast⟩
    have hfil : (({(L' ++ [b]).drop ((L' ++ [b]).length - m)} : Finset (List ℕ)).filter
        (fun _ => b = c)).card ≤ if b = c then 1 else 0 := by
      by_cases hbc : b = c <;> simp [hbc]
    calc (infSet (L' ++ [b]) m c).card
        ≤ (infSet L' m c ∪ ({(L' ++ [b]).drop ((L' ++ [b]).length - m)} : Finset (List ℕ)).filter
            (fun _ => b = c)).card := Finset.card_le_card hsub
      _ ≤ (infSet L' m c).card + (({(L' ++ [b]).drop ((L' ++ [b]).length - m)} :
            Finset (List ℕ)).filter (fun _ => b = c)).card := Finset.card_union_le _ _
      _ ≤ L'.count c + (if b = c then 1 else 0) := by omega
      _ = (L' ++ [b]).count c := by
        rw [List.count_append]
        by_cases hbc : b = c <;> simp [hbc]

lemma digits_block {c k v : ℕ} (hc1 : 1 ≤ c) (hc9 : c ≤ 9) (hv1 : c * 10 ^ k ≤ v)
    (hv2 : v < (c + 1) * 10 ^ k) : (D v).length = k + 1 ∧ (D v).getLast? = some c := by
  have hv2' : v < c * 10 ^ k + 10 ^ k := by rw [add_mul, one_mul] at hv2; exact hv2
  have hrlt : v - c * 10 ^ k < 10 ^ k := by omega
  have hlen : (D (v - c * 10 ^ k)).length ≤ k :=
    (Nat.digits_length_le_iff (by norm_num) _).mpr hrlt
  have key := Nat.digits_append_zeroes_append_digits (b := 10) (k := k - (D (v - c * 10 ^ k)).length)
    (m := c) (n := v - c * 10 ^ k) (by norm_num) (by omega)
  have hk : (D (v - c * 10 ^ k)).length + (k - (D (v - c * 10 ^ k)).length) = k := by omega
  rw [hk] at key
  have hv : v - c * 10 ^ k + 10 ^ k * c = v := by rw [mul_comm (10 ^ k) c]; omega
  have hcd : Nat.digits 10 c = [c] := digits_single hc1 hc9
  rw [hv, hcd] at key
  show (Nat.digits 10 v).length = k + 1 ∧ (Nat.digits 10 v).getLast? = some c
  rw [← key]
  constructor
  · simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  · simp

lemma block_count {n c k S : ℕ} (hc1 : 1 ≤ c) (hc9 : c ≤ 9)
    (hcov : ∀ v, 1 ≤ v → v ≤ S → D v <:+: D n) (hS : (c + 1) * 10 ^ k ≤ S + 1) :
    10 ^ k ≤ (D n).count c := by
  have hpos : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have hck : 1 ≤ c * 10 ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hmaps : ∀ v ∈ Finset.Ico (c * 10 ^ k) ((c + 1) * 10 ^ k), D v ∈ infSet (D n) (k + 1) c := by
    intro v hv
    rw [Finset.mem_Ico] at hv
    obtain ⟨hl, hlast⟩ := digits_block hc1 hc9 hv.1 hv.2
    rw [mem_infSet]
    exact ⟨hcov v (by omega) (by omega), hl, hlast⟩
  have hinj : Set.InjOn (fun v => D v) (Finset.Ico (c * 10 ^ k) ((c + 1) * 10 ^ k) : Set ℕ) :=
    fun a _ b _ hab => Nat.digits.injective 10 hab
  have hcard := Finset.card_le_card_of_injOn (fun v => D v) hmaps hinj
  have hc2 := card_infSet c (k + 1) (by omega) (D n)
  rw [Nat.card_Ico] at hcard
  have : (c + 1) * 10 ^ k - c * 10 ^ k = 10 ^ k := by rw [add_mul, one_mul]; omega
  omega

lemma sums_upto_45 : ∀ w, w ≤ 45 → ∃ u, u <+ ([1, 2, 3, 4, 5, 6, 7, 8, 9] : List ℕ) ∧ u.sum = w := by
  intro w hw
  interval_cases w
  · exact ⟨[], by decide, by rfl⟩
  · exact ⟨[1], by decide, by rfl⟩
  · exact ⟨[2], by decide, by rfl⟩
  · exact ⟨[3], by decide, by rfl⟩
  · exact ⟨[4], by decide, by rfl⟩
  · exact ⟨[5], by decide, by rfl⟩
  · exact ⟨[6], by decide, by rfl⟩
  · exact ⟨[7], by decide, by rfl⟩
  · exact ⟨[8], by decide, by rfl⟩
  · exact ⟨[9], by decide, by rfl⟩
  · exact ⟨[1, 9], by decide, by rfl⟩
  · exact ⟨[2, 9], by decide, by rfl⟩
  · exact ⟨[3, 9], by decide, by rfl⟩
  · exact ⟨[4, 9], by decide, by rfl⟩
  · exact ⟨[5, 9], by decide, by rfl⟩
  · exact ⟨[6, 9], by decide, by rfl⟩
  · exact ⟨[7, 9], by decide, by rfl⟩
  · exact ⟨[8, 9], by decide, by rfl⟩
  · exact ⟨[1, 8, 9], by decide, by rfl⟩
  · exact ⟨[2, 8, 9], by decide, by rfl⟩
  · exact ⟨[3, 8, 9], by decide, by rfl⟩
  · exact ⟨[4, 8, 9], by decide, by rfl⟩
  · exact ⟨[5, 8, 9], by decide, by rfl⟩
  · exact ⟨[6, 8, 9], by decide, by rfl⟩
  · exact ⟨[7, 8, 9], by decide, by rfl⟩
  · exact ⟨[1, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[2, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[3, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[4, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[5, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[6, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[1, 6, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[2, 6, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[3, 6, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[4, 6, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[5, 6, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[1, 5, 6, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[2, 5, 6, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[3, 5, 6, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[4, 5, 6, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[1, 4, 5, 6, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[2, 4, 5, 6, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[3, 4, 5, 6, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[1, 3, 4, 5, 6, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[2, 3, 4, 5, 6, 7, 8, 9], by decide, by rfl⟩
  · exact ⟨[1, 2, 3, 4, 5, 6, 7, 8, 9], by decide, by rfl⟩

lemma cover {n : ℕ} (h : IsTerm n) (hc : 2 ≤ (D n).count 1) :
    ∀ v, 1 ≤ v → v ≤ (NZ n).sum → D v <:+: D n := by
  have hall := all_mem h hc
  have h19 : [1, 2, 3, 4, 5, 6, 7, 8, 9] <+~ NZ n := by
    rw [List.subperm_ext_iff]
    intro x hx
    have hx1 : 1 ≤ x := by simp at hx; omega
    have hx9 : x ≤ 9 := by simp at hx; omega
    have hx' : x ∈ NZ n := mem_nz (by omega) (hall x hx1 hx9)
    have hc1 : List.count x [1, 2, 3, 4, 5, 6, 7, 8, 9] = 1 := by
      interval_cases x <;> rfl
    rw [hc1]
    exact List.count_pos_iff.mpr hx'
  obtain ⟨l0, hl1, hl2⟩ := h19
  obtain ⟨r, hr0⟩ := hl2.exists_perm_append
  have hr : NZ n ~ [1, 2, 3, 4, 5, 6, 7, 8, 9] ++ r := hr0.trans (hl1.append_right r)
  have hsum : (NZ n).sum = 45 + r.sum := by rw [hr.sum_eq]; simp; omega
  have hr9 : ∀ x ∈ r, x ≤ 9 := fun x hx => nz_le9 (hr.symm.subset (List.mem_append_right _ hx))
  intro v hv1 hv
  obtain ⟨k, hk1, hk2⟩ : ∃ k, v - 45 ≤ (r.take k).sum ∧ (r.take k).sum ≤ v := by
    by_cases hv45 : v ≤ 45
    · exact ⟨0, by simp; omega, by simp⟩
    · obtain ⟨k, h1, h2⟩ := prefix_window r hr9 (v - 45) (by omega)
      exact ⟨k, h1, by omega⟩
  obtain ⟨u, hu, hus⟩ := sums_upto_45 (v - (r.take k).sum) (by omega)
  have hsub : u ++ r.take k <+ [1, 2, 3, 4, 5, 6, 7, 8, 9] ++ r :=
    hu.append (List.take_sublist _ _)
  have hsp : u ++ r.take k <+~ D n :=
    (hsub.subperm.trans hr.symm.subperm).trans (nz_sublist n).subperm
  have hsv : (u ++ r.take k).sum = v := by rw [List.sum_append, hus]; omega
  have hne : u ++ r.take k ≠ [] := by
    intro h0; rw [h0] at hsv; simp at hsv; omega
  have := term_subperm h hsp hne
  rwa [hsv] at this

lemma sum_counts (l : List ℕ) (hl : ∀ x ∈ l, x ≤ 9) :
    l.sum = l.count 1 + 2 * l.count 2 + 3 * l.count 3 + 4 * l.count 4 + 5 * l.count 5 +
      6 * l.count 6 + 7 * l.count 7 + 8 * l.count 8 + 9 * l.count 9 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := hl a (by simp)
    have ih' := ih (fun x hx => hl x (by simp [hx]))
    simp only [List.sum_cons, List.count_cons, ih']
    interval_cases a <;> simp <;> omega

/-- Main counting step: two 1s force every digit, then every value up to the digit sum is a
block, and counting blocks by their leading digit makes the digit sum exceed every power of 10. -/
lemma no_two_ones {n : ℕ} (h : IsTerm n) : (D n).count 1 ≤ 1 := by
  by_contra hc
  replace hc : 2 ≤ (D n).count 1 := by omega
  have hcov := cover h hc
  have hall := all_mem h hc
  have hS := sum_counts (NZ n) (fun x hx => nz_le9 hx)
  simp only [count_nz (show (1:ℕ) ≠ 0 by norm_num), count_nz (show (2:ℕ) ≠ 0 by norm_num),
    count_nz (show (3:ℕ) ≠ 0 by norm_num), count_nz (show (4:ℕ) ≠ 0 by norm_num),
    count_nz (show (5:ℕ) ≠ 0 by norm_num), count_nz (show (6:ℕ) ≠ 0 by norm_num),
    count_nz (show (7:ℕ) ≠ 0 by norm_num), count_nz (show (8:ℕ) ≠ 0 by norm_num),
    count_nz (show (9:ℕ) ≠ 0 by norm_num)] at hS
  have hpos : ∀ c, 1 ≤ c → c ≤ 9 → 1 ≤ (D n).count c :=
    fun c h1 h9 => List.count_pos_iff.mpr (hall c h1 h9)
  have p1 := hpos 1 le_rfl (by norm_num); have p2 := hpos 2 (by norm_num) (by norm_num)
  have p3 := hpos 3 (by norm_num) (by norm_num); have p4 := hpos 4 (by norm_num) (by norm_num)
  have p5 := hpos 5 (by norm_num) (by norm_num); have p6 := hpos 6 (by norm_num) (by norm_num)
  have p7 := hpos 7 (by norm_num) (by norm_num); have p8 := hpos 8 (by norm_num) (by norm_num)
  have p9 := hpos 9 (by norm_num) (by norm_num)
  have blk : ∀ c k, 1 ≤ c → c ≤ 9 → (c + 1) * 10 ^ k ≤ (NZ n).sum + 1 → 10 ^ k ≤ (D n).count c :=
    fun c k h1 h9 hle => block_count h1 h9 hcov hle
  have Q : ∀ l, 10 ^ (l + 2) ≤ (NZ n).sum + 1 := by
    intro l
    induction l with
    | zero =>
      have b1 := blk 1 1 le_rfl (by norm_num) (by norm_num; omega)
      have b2 := blk 2 1 (by norm_num) (by norm_num) (by norm_num; omega)
      have b3 := blk 3 1 (by norm_num) (by norm_num) (by norm_num; omega)
      norm_num at b1 b2 b3 ⊢
      omega
    | succ l ih =>
      have f : ∀ c, 1 ≤ c → c ≤ 9 → (c + 1) * 10 ^ (l + 1) ≤ (NZ n).sum + 1 →
          10 ^ (l + 1) ≤ (D n).count c := fun c h1 h9 hle => blk c (l + 1) h1 h9 hle
      have g : ∀ c, 1 ≤ c → c ≤ 9 → (c + 1) * (10 * 10 ^ (l + 1)) ≤ (NZ n).sum + 1 →
          10 * 10 ^ (l + 1) ≤ (D n).count c := by
        intro c h1 h9 hle
        have e : 10 ^ (l + 2) = 10 * 10 ^ (l + 1) := by ring
        have := blk c (l + 2) h1 h9 (by rw [e]; exact hle)
        rwa [e] at this
      have e1 : 10 ^ (l + 1 + 2) = 100 * 10 ^ (l + 1) := by ring
      have e2 : 10 ^ (l + 2) = 10 * 10 ^ (l + 1) := by ring
      rw [e1]
      rw [e2] at ih
      generalize 10 ^ (l + 1) = X at f g ih ⊢
      have f1 := f 1 le_rfl (by norm_num) (by omega)
      have f2 := f 2 (by norm_num) (by norm_num) (by omega)
      have f3 := f 3 (by norm_num) (by norm_num) (by omega)
      have f4 := f 4 (by norm_num) (by norm_num) (by omega)
      have f5 := f 5 (by norm_num) (by norm_num) (by omega)
      have f6 := f 6 (by norm_num) (by norm_num) (by omega)
      have f7 := f 7 (by norm_num) (by norm_num) (by omega)
      have f8 := f 8 (by norm_num) (by norm_num) (by omega)
      have f9 := f 9 (by norm_num) (by norm_num) (by omega)
      have g1 := g 1 le_rfl (by norm_num) (by omega)
      have g2 := g 2 (by norm_num) (by norm_num) (by omega)
      have g3 := g 3 (by norm_num) (by norm_num) (by omega)
      have g4 := g 4 (by norm_num) (by norm_num) (by omega)
      have g5 := g 5 (by norm_num) (by norm_num) (by omega)
      have g6 := g 6 (by norm_num) (by norm_num) (by omega)
      have g7 := g 7 (by norm_num) (by norm_num) (by omega)
      have g8 := g 8 (by norm_num) (by norm_num) (by omega)
      omega
  have hQ := Q (NZ n).sum
  have hlt : (NZ n).sum + 2 < 10 ^ ((NZ n).sum + 2) := Nat.lt_pow_self (by norm_num)
  omega

lemma elems_19 {n : ℕ} (h : IsTerm n) (hc1 : (D n).count 1 = 1) :
    ∀ x ∈ NZ n, x = 1 ∨ x = 9 := by
  intro x hx
  have h1 := nz_pos hx
  have h9 := nz_le9 hx
  have hxD := (List.mem_filter.mp hx).1
  by_contra hne
  push Not at hne
  exact no_mid h hc1 x (by omega) (by omega) hxD

lemma counts_19 : ∀ l : List ℕ, (∀ x ∈ l, x = 1 ∨ x = 9) →
    l.length = l.count 1 + l.count 9 ∧ l.sum = l.count 1 + 9 * l.count 9
  | [], _ => by simp
  | a :: t, hl => by
    obtain ⟨ih1, ih2⟩ := counts_19 t (fun x hx => hl x (by simp [hx]))
    rcases hl a (by simp) with rfl | rfl <;> simp [ih1, ih2] <;> omega

lemma sum_filter_nz (l : List ℕ) : (l.filter (fun x => x ≠ 0)).sum = l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases ha : a = 0
    · rw [List.filter_cons_of_neg (by simpa using ha), ih, ha]; simp
    · rw [List.filter_cons_of_pos (by simpa using ha), List.sum_cons, ih, List.sum_cons]

lemma singleton_infix {d : ℕ} {L : List ℕ} (h : d ∈ L) : [d] <:+: L := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem h
  exact ⟨s, t, by simp⟩

lemma forward {n : ℕ} (h : IsTerm n) :
    (NZ n).length ≤ 1 ∨ ((NZ n).Perm [1, 9] ∧ [0, 1] <:+: D n) := by
  by_cases hlen : (NZ n).length ≤ 1
  · exact Or.inl hlen
  right
  have h1 := one_mem_digits h (by omega)
  have hc1 : (D n).count 1 = 1 := by
    have := no_two_ones h
    have := List.count_pos_iff.mpr h1
    omega
  have hel := elems_19 h hc1
  obtain ⟨hl, -⟩ := counts_19 (NZ n) hel
  have hn1 : (NZ n).count 1 = 1 := by rw [count_nz (by norm_num)]; exact hc1
  have hn9 : (NZ n).count 9 = 1 := by
    have := no_two_nines h hc1
    rw [← count_nz (by norm_num)] at this
    omega
  have h9 : 9 ∈ D n := (List.mem_filter.mp (List.count_pos_iff.mp (by omega : 0 < (NZ n).count 9))).1
  refine ⟨?_, ?_⟩
  · rw [List.perm_iff_count]
    intro a
    by_cases a1 : a = 1
    · subst a1; simp [hn1]
    by_cases a9 : a = 9
    · subst a9; simp [hn9]
    have : a ∉ NZ n := fun ha => by rcases hel a ha with rfl | rfl <;> simp_all
    rw [List.count_eq_zero.mpr this]
    simp [Ne.symm a1, Ne.symm a9]
  · have := term_subperm h (subperm_pair (a := 1) (b := 9) (by norm_num) h1 h9) (by simp)
    simpa using this

lemma backward {n : ℕ}
    (hn : (NZ n).length ≤ 1 ∨ ((NZ n).Perm [1, 9] ∧ [0, 1] <:+: D n)) : IsTerm n := by
  intro l hl _
  have hsub : l.filter (fun x => x ≠ 0) <+ NZ n := hl.filter _
  rw [← sum_filter_nz l]
  rcases hn with hlen | ⟨hp, h10⟩
  · have hlen' := hsub.length_le
    generalize l.filter (fun x => x ≠ 0) = f at hsub hlen' ⊢
    rcases f with _ | ⟨d, _ | ⟨e, r⟩⟩
    · simp
    · have hd : d ∈ NZ n := hsub.subset (by simp)
      simp only [List.sum_cons, List.sum_nil, add_zero]
      rw [digits_single (nz_pos hd) (nz_le9 hd)]
      exact singleton_infix (List.mem_filter.mp hd).1
    · simp at hlen'; omega
  · set l' := l.filter (fun x => x ≠ 0)
    have hsp : l' <+~ [1, 9] := hsub.subperm.trans hp.subperm
    have hel : ∀ x ∈ l', x = 1 ∨ x = 9 := by
      intro x hx
      have := hsp.subset hx
      simpa using this
    obtain ⟨-, hs⟩ := counts_19 l' hel
    have c1 : l'.count 1 ≤ 1 := by simpa using hsp.count_le 1
    have c9 : l'.count 9 ≤ 1 := by simpa using hsp.count_le 9
    have h1 : 1 ∈ D n := (List.mem_filter.mp (hp.symm.subset (by simp : (1 : ℕ) ∈ [1, 9]))).1
    have h9 : 9 ∈ D n := (List.mem_filter.mp (hp.symm.subset (by simp : (9 : ℕ) ∈ [1, 9]))).1
    rw [hs]
    interval_cases hc : l'.count 1 <;> interval_cases hd : l'.count 9
    · simp
    · simpa using singleton_infix h9
    · simpa using singleton_infix h1
    · simpa using h10

/-- A202272: n is a term iff it has at most one nonzero digit, or its nonzero digits are one 1
and one 9 with the 1 immediately followed by a 0 (the block "10"). -/
theorem A202272_main (n : ℕ) :
    IsTerm n ↔ (NZ n).length ≤ 1 ∨ ((NZ n).Perm [1, 9] ∧ [0, 1] <:+: D n) :=
  ⟨forward, backward⟩
