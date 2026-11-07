import Mathlib

/-!
# OEIS A176948: for every n >= 4, n != 6, some n-gonal number is not k-gonal for 3 <= k < n

Definition. `IsPolygonal k N` : N is a k-gonal number, N = m((k-2)m - k + 4)/2 for some m >= 0,
written as 2N = (k-2) m (m-1) + 2m.

Main result.
* `A176948_conjecture` : for n >= 4, n != 6 there is N with `IsPolygonal n N` and
  `¬ IsPolygonal k N` for every 3 <= k < n. Equivalently A176774(N) = n, so A176948(n) != 0.

Route. With a = n-2, b = k-2, X = 2aj - (a-2), Y = 2bi - (b-2), C = b(a-2)^2 - a(b-2)^2 =
(a-b)(ab-4): if N = P_n(j) = P_k(i) then a(bX^2 - C) = (aY)^2 (`key_identity`). C != 0 unless
n = 6 (k = 3). For a prime p > 3 not dividing abC some x makes a(bx^2 - C) a non-square mod p
(`exists_nonsq`: otherwise s -> a(bs - C) permutes the squares of ZMod p, and comparing sums with
sum of squares = 0 gives aC #squares = 0). One prime per k (distinct, > n^3), CRT for j.

Checked: everything. No `sorry`, no `native_decide`.
-/

open Finset

def IsPolygonal (k N : ℕ) : Prop := ∃ m : ℕ, 2 * N = (k - 2) * (m * (m - 1)) + 2 * m

lemma two_ne_zero_zmod (p : ℕ) [Fact p.Prime] (hp : 2 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)

/-- Sum of the squares (as a set) in ZMod p is 0 for p > 3. -/
lemma sum_squares_zero (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    ∑ s ∈ (univ : Finset (ZMod p)).image (fun x => x ^ 2), s = 0 := by
  have h2 := two_ne_zero_zmod p (by omega)
  have hsum : ∑ x : ZMod p, x ^ 2 = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2 (by rw [ZMod.card]; omega)
  have key : ∑ x : ZMod p, x ^ 2 =
      ∑ s ∈ (univ : Finset (ZMod p)).image (fun x => x ^ 2), (2 : ZMod p) * s := by
    rw [Finset.sum_comp (fun s : ZMod p => s) (fun x : ZMod p => x ^ 2)]
    apply sum_congr rfl
    intro s hs
    obtain ⟨y, -, rfl⟩ := mem_image.mp hs
    by_cases hy : y = 0
    · simp [hy]
    · have hne : y ≠ -y := by
        intro h
        have : (2 : ZMod p) * y = 0 := by linear_combination h
        rcases mul_eq_zero.mp this with h' | h'
        · exact h2 h'
        · exact hy h'
      have hf : (univ.filter (fun x : ZMod p => x ^ 2 = y ^ 2)) = {y, -y} := by
        ext x; simp [sq_eq_sq_iff_eq_or_eq_neg]
      rw [hf, card_pair hne]
      simp [two_smul, two_mul]
  rw [hsum, ← mul_sum] at key
  exact (mul_eq_zero.mp key.symm).resolve_left h2

/-- Some value a(b x^2 - C) is a non-square mod p. -/
lemma exists_nonsq (p : ℕ) [Fact p.Prime] (hp : 3 < p) (a b C : ZMod p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hC : C ≠ 0) : ∃ x : ZMod p, ¬ IsSquare (a * (b * x ^ 2 - C)) := by
  by_contra hcon
  push Not at hcon
  set S := (univ : Finset (ZMod p)).image (fun x => x ^ 2) with hS
  have memS : ∀ t, t ∈ S ↔ IsSquare t := by
    intro t
    simp only [hS, mem_image, mem_univ, true_and, IsSquare, sq]
    constructor
    · rintro ⟨r, rfl⟩; exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩; exact ⟨r, rfl⟩
  set f : ZMod p → ZMod p := fun s => a * (b * s - C) with hf
  have hmap : ∀ s ∈ S, f s ∈ S := by
    intro s hs
    obtain ⟨x, -, rfl⟩ := mem_image.mp hs
    exact (memS _).mpr (hcon x)
  have hinj : Set.InjOn f S := by
    intro s _ t _ h
    have h' : a * b * (s - t) = 0 := by simp only [hf] at h; linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact absurd h1 (mul_ne_zero ha hb)
    · exact sub_eq_zero.mp h1
  have himg : S.image f = S :=
    eq_of_subset_of_card_le (image_subset_iff.mpr hmap) (card_image_of_injOn hinj).ge
  have hsum : ∑ s ∈ S, f s = ∑ s ∈ S, s := by
    calc ∑ s ∈ S, f s = ∑ s ∈ S.image f, s := (sum_image (f := fun s => s) hinj).symm
      _ = ∑ s ∈ S, s := by rw [himg]
  have h0 := sum_squares_zero p hp
  rw [← hS] at h0
  have e : ∑ s ∈ S, f s = a * b * ∑ s ∈ S, s - S.card • (a * C) := by
    calc ∑ s ∈ S, f s = ∑ s ∈ S, (a * b * s - a * C) :=
          sum_congr rfl (fun s _ => by simp only [hf]; ring)
      _ = a * b * ∑ s ∈ S, s - S.card • (a * C) := by rw [sum_sub_distrib, mul_sum, sum_const]
  rw [e, h0, nsmul_eq_mul] at hsum
  have hcardS : (S.card : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have hpos : 0 < S.card := card_pos.mpr ⟨0, (memS 0).mpr ⟨0, by ring⟩⟩
    have hlt : S.card < p := by
      obtain ⟨r, hr⟩ := FiniteField.exists_nonsquare (F := ZMod p)
        (by rw [ZMod.ringChar_zmod_n]; omega)
      have hss : S ⊂ univ := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨subset_univ _, fun h => hr ((memS r).mp (h ▸ mem_univ r))⟩
      have := card_lt_card hss
      rwa [card_univ, ZMod.card] at this
    exact absurd (Nat.le_of_dvd hpos h) (by omega)
  have : a * C * (S.card : ZMod p) = 0 := by linear_combination -hsum
  rcases mul_eq_zero.mp this with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact ha h2
    · exact hC h2
  · exact hcardS h1

lemma cast_mul_pred (m : ℕ) : ((m * (m - 1) : ℕ) : ℤ) = (m : ℤ) * ((m : ℤ) - 1) := by
  cases m with
  | zero => simp
  | succ m => push_cast; simp

/-- The integer identity behind the obstruction. -/
lemma key_identity (A B J I N2 : ℤ) (hj : N2 = A * (J * (J - 1)) + 2 * J)
    (hi : N2 = B * (I * (I - 1)) + 2 * I) :
    A * (B * (2 * A * J - (A - 2)) ^ 2 - (B * (A - 2) ^ 2 - A * (B - 2) ^ 2)) =
      (A * (2 * B * I - (B - 2))) ^ 2 := by
  linear_combination (-4 * A ^ 2 * B) * hj + (4 * A ^ 2 * B) * hi

/-- The prime attached to k. -/
noncomputable def pk (n k : ℕ) : ℕ := Nat.nth Nat.Prime (n ^ 3 + k)

lemma pk_prime (n k : ℕ) : (pk n k).Prime := Nat.prime_nth_prime _

lemma pk_ge (n k : ℕ) : n ^ 3 + k + 2 ≤ pk n k := Nat.add_two_le_nth_prime _

lemma natCast_ne_zero_of_lt (p m : ℕ) (h0 : 0 < m) (hm : m < p) : (m : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd h0 h) (by omega)

lemma C_bounds (n a b : ℕ) (hn : 4 ≤ n) (ha : a = n - 2) (hb1 : 1 ≤ b) (hba : b < a) (ha4 : a ≠ 4) :
    (b : ℤ) * ((a : ℤ) - 2) ^ 2 - a * ((b : ℤ) - 2) ^ 2 ≠ 0 ∧
    |(b : ℤ) * ((a : ℤ) - 2) ^ 2 - a * ((b : ℤ) - 2) ^ 2| < (n : ℤ) ^ 3 := by
  have hfac : (b : ℤ) * ((a : ℤ) - 2) ^ 2 - a * ((b : ℤ) - 2) ^ 2 =
      ((a : ℤ) - b) * ((a : ℤ) * b - 4) := by ring
  rw [hfac]
  have hab : (a : ℤ) * b ≠ 4 := by
    intro h
    have h' : a * b = 4 := by exact_mod_cast h
    rcases (by omega : b = 1 ∨ b = 2 ∨ 3 ≤ b) with hb | hb | hb
    · subst hb; omega
    · subst hb; omega
    · have : 4 * 3 ≤ a * b := Nat.mul_le_mul (by omega) hb
      omega
  have h1 : (0 : ℤ) < a - b := by have : (b : ℤ) < a := by exact_mod_cast hba
                                  linarith
  have hna : (a : ℤ) < n := by have : a < n := by omega
                               exact_mod_cast this
  have hbn : (b : ℤ) < n := by linarith [show (b : ℤ) < a from by exact_mod_cast hba]
  have hb0 : (1 : ℤ) ≤ b := by exact_mod_cast hb1
  have hn4 : (4 : ℤ) ≤ n := by exact_mod_cast hn
  refine ⟨mul_ne_zero h1.ne' (sub_ne_zero.mpr hab), ?_⟩
  rw [abs_lt]
  have hab2 : (a : ℤ) * b < (n : ℤ) ^ 2 := by nlinarith
  have hab0 : (0 : ℤ) ≤ (a : ℤ) * b := by positivity
  constructor <;> nlinarith

theorem A176948_conjecture (n : ℕ) (hn : 4 ≤ n) (h6 : n ≠ 6) :
    ∃ N, IsPolygonal n N ∧ ∀ k, 3 ≤ k → k < n → ¬ IsPolygonal k N := by
  set a := n - 2 with ha
  have ha4 : a ≠ 4 := by omega
  -- residue choice for each k
  have hres : ∀ k ∈ Ico 3 n, ∃ r : ℕ, ∀ j : ℕ, j ≡ r [MOD pk n k] →
      ¬ IsSquare (((a : ℤ) * ((k - 2 : ℕ) * (2 * a * j - ((a : ℤ) - 2)) ^ 2 -
        ((k - 2 : ℕ) * ((a : ℤ) - 2) ^ 2 - a * (((k - 2 : ℕ) : ℤ) - 2) ^ 2)) : ℤ) :
          ZMod (pk n k)) := by
    intro k hk
    rw [mem_Ico] at hk
    set p := pk n k
    have : Fact p.Prime := ⟨pk_prime n k⟩
    have hp := pk_ge n k
    have hn3 : n ≤ n ^ 3 := by
      calc n = n ^ 1 := (pow_one n).symm
        _ ≤ n ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    set b := k - 2 with hb
    obtain ⟨hC0, hCb⟩ := C_bounds n a b hn ha (by omega) (by omega) ha4
    set C : ℤ := (b : ℤ) * ((a : ℤ) - 2) ^ 2 - a * ((b : ℤ) - 2) ^ 2 with hCdef
    have haz : ((a : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt p a (by omega) (by omega)
    have hbz : ((b : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt p b (by omega) (by omega)
    have hCz : ((C : ℤ) : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
      obtain ⟨c, hc⟩ := h
      have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact hC0 hc
      have hpz : ((n : ℤ) ^ 3 + 2) ≤ (p : ℤ) := by
        have : n ^ 3 + 2 ≤ p := by omega
        exact_mod_cast this
      rw [abs_lt] at hCb
      rcases (by omega : 1 ≤ c ∨ c ≤ -1) with h1 | h1
      · nlinarith
      · nlinarith
    obtain ⟨x, hx⟩ := exists_nonsq p (by omega) _ _ _ haz hbz hCz
    have h2 := two_ne_zero_zmod p (by omega)
    set j0 : ZMod p := (x + ((a : ZMod p) - 2)) * (2 * (a : ZMod p))⁻¹
    refine ⟨j0.val, fun j hj => ?_⟩
    have hjc : (j : ZMod p) = j0 := by
      rw [← ZMod.natCast_zmod_val j0]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hj
    have hX : 2 * (a : ZMod p) * (j : ZMod p) - ((a : ZMod p) - 2) = x := by
      rw [hjc]
      simp only [j0]
      field_simp
      ring
    push_cast
    rw [hX]
    simpa [hCdef] using hx
  choose r hr using hres
  let rr : ℕ → ℕ := fun k => if h : k ∈ Ico 3 n then r k h else 0
  have hcop : Set.Pairwise (Ico 3 n : Set ℕ) (Function.onFun Nat.Coprime (pk n)) := by
    intro k1 _ k2 _ hne
    exact (Nat.coprime_primes (pk_prime n k1) (pk_prime n k2)).mpr
      (fun h => hne (by
        have := Nat.nth_injective Nat.infinite_setOfPred_prime h
        omega))
  obtain ⟨j, hj⟩ := Nat.chineseRemainderOfFinset rr (pk n) (Ico 3 n)
    (fun k _ => (pk_prime n k).ne_zero) hcop
  have heven : 2 ∣ j * (j - 1) := by
    rcases Nat.even_or_odd j with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t * (j - 1), by subst ht; ring⟩
    · exact ⟨j * t, by subst ht; simp; ring⟩
  refine ⟨a * (j * (j - 1) / 2) + j, ⟨j, ?_⟩, ?_⟩
  · rw [← ha]; obtain ⟨t, ht⟩ := heven; rw [ht]; simp; ring
  · intro k hk3 hkn ⟨i, hi⟩
    have hkI : k ∈ Ico 3 n := mem_Ico.mpr ⟨hk3, hkn⟩
    have hjr : j ≡ r k hkI [MOD pk n k] := by
      have := hj k hkI
      simp only [rr, hkI, ↓reduceDIte] at this
      exact this
    apply hr k hkI j hjr
    set N := a * (j * (j - 1) / 2) + j
    have hjN : ((2 * N : ℕ) : ℤ) = (a : ℤ) * ((j : ℤ) * ((j : ℤ) - 1)) + 2 * j := by
      obtain ⟨t, ht⟩ := heven
      have : 2 * N = a * (j * (j - 1)) + 2 * j := by simp only [N]; rw [ht]; simp; ring
      rw [this, Nat.cast_add, Nat.cast_mul, cast_mul_pred]; push_cast; ring
    have hiN : ((2 * N : ℕ) : ℤ) = ((k - 2 : ℕ) : ℤ) * ((i : ℤ) * ((i : ℤ) - 1)) + 2 * i := by
      rw [hi, Nat.cast_add, Nat.cast_mul, cast_mul_pred]; push_cast; ring
    have hid := key_identity (a : ℤ) ((k - 2 : ℕ) : ℤ) j i _ hjN hiN
    rw [hid]
    exact ⟨_, (Int.cast_pow _ 2).trans (sq _)⟩
