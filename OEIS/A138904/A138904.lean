/-
OEIS A138904: a(m) = number of rotational symmetries of the binary expansion of m.

Checked here (core Lean, no Mathlib), for every length L ≥ 1:
* `symCount_dvd`: the number of rotations k ∈ [0, L) fixing an L-bit word divides L.
* `A138904_dvd`, `A138904_values`: for m of binary length L, a(m) ∣ L, and every
  divisor e of L equals a(m) for some m of length L (first conjecture).
* `A138904_eq_length_iff`: a(m) = L iff m = 2^L - 1.
* `A138904_prime_block`: for a prime d ∣ L with d < L, a(m) = L/d iff
  m = R·a with R = 1 + 2^d + ... + 2^(L-d) and 2^(d-1) ≤ a < 2^d - 1.
* `A138904_rest`: if the divisors of L strictly between 1 and L are pairwise
  coprime, every other m of length L has a(m) = 1 (second conjecture).
Not checked here: that `A138904` (rotations of the bit list of m, read through
`Nat.testBit`, length `Nat.log2 m + 1`) is the OEIS definition; the script
certificate/check.py compares it with the listed terms.
-/

/-- Rotation by k fixes the L low bits of m. -/
def symAt (L m k : Nat) : Bool :=
  (List.range L).all (fun i => m.testBit ((i + k) % L) == m.testBit i)

/-- Number of rotations k ∈ [0, L) fixing the L-bit word m. -/
def symCount (L m : Nat) : Nat := ((List.range L).filter (symAt L m)).length

/-- a(m); m = 0 has expansion "0" of length 1. -/
def A138904 (m : Nat) : Nat := symCount (m.log2 + 1) m

/-- R d e = 1 + 2^d + ... + 2^((e-1)d). -/
def R (d : Nat) : Nat → Nat
  | 0 => 0
  | e + 1 => 2 ^ d * R d e + 1

/-- d is prime (core has no `Nat.Prime`). -/
def IsPrime (d : Nat) : Prop := 2 ≤ d ∧ ∀ k, k ∣ d → k = 1 ∨ k = d

section
variable {L m : Nat}

def S (L m k : Nat) : Prop := ∀ i, i < L → m.testBit ((i + k) % L) = m.testBit i

theorem symAt_iff (L m k : Nat) : symAt L m k = true ↔ S L m k := by
  simp [symAt, S, List.all_eq_true, List.mem_range]

theorem S_zero (L m : Nat) : S L m 0 := by
  intro i hi; rw [Nat.add_zero, Nat.mod_eq_of_lt hi]

theorem S_L (L m : Nat) : S L m L := by
  intro i hi; rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi]

theorem S_add (hL : 0 < L) {k j : Nat} (hk : S L m k) (hj : S L m j) : S L m (k + j) := by
  intro i hi
  have h1 := hk ((i + j) % L) (Nat.mod_lt _ hL)
  rw [Nat.mod_add_mod] at h1
  rw [show i + (k + j) = i + j + k by omega, h1, hj i hi]

theorem S_mul (hL : 0 < L) {k : Nat} (hk : S L m k) (n : Nat) : S L m (k * n) := by
  induction n with
  | zero => rw [Nat.mul_zero]; exact S_zero L m
  | succ n ih => rw [Nat.mul_succ]; exact S_add hL ih hk

theorem S_sub (hL : 0 < L) {k j : Nat} (hkj : k ≤ j) (hk : S L m k) (hj : S L m j) :
    S L m (j - k) := by
  intro i hi
  have h1 := hk ((i + (j - k)) % L) (Nat.mod_lt _ hL)
  rw [Nat.mod_add_mod, show i + (j - k) + k = i + j by omega, hj i hi] at h1
  exact h1.symm

theorem exists_min (P : Nat → Prop) (n : Nat) (h : P n) : ∃ p, P p ∧ ∀ k, k < p → ¬ P k := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases Classical.em (∃ k, k < n ∧ P k) with
    | inl hx => obtain ⟨k, hk, hP⟩ := hx; exact ih k hk hP
    | inr hx => exact ⟨n, h, fun k hk hP => hx ⟨k, hk, hP⟩⟩

/-- The least positive period p: S k ↔ p ∣ k, and p ∣ L. -/
theorem period (hL : 0 < L) (m : Nat) :
    ∃ p, 0 < p ∧ p ∣ L ∧ ∀ k, S L m k ↔ p ∣ k := by
  obtain ⟨p, ⟨hp0, hp⟩, hmin⟩ :=
    exists_min (fun k => 0 < k ∧ S L m k) L ⟨hL, S_L L m⟩
  have key : ∀ k, S L m k → p ∣ k := by
    intro k hk
    have h1 : S L m (k - p * (k / p)) :=
      S_sub hL (Nat.mul_div_le k p) (S_mul hL hp _) hk
    have h2 : k - p * (k / p) = k % p := by
      have := Nat.mod_add_div k p; omega
    rw [h2] at h1
    have h3 : k % p < p := Nat.mod_lt _ hp0
    have h4 : k % p = 0 := by
      apply Classical.byContradiction; intro hne
      exact hmin _ h3 ⟨Nat.pos_of_ne_zero hne, h1⟩
    exact Nat.dvd_of_mod_eq_zero h4
  refine ⟨p, hp0, key L (S_L L m), fun k => ⟨key k, ?_⟩⟩
  rintro ⟨c, rfl⟩
  exact S_mul hL hp c

theorem filter_dvd_range (p : Nat) (hp : 0 < p) (e : Nat) :
    (List.range (p * e)).filter (fun k => decide (p ∣ k)) = (List.range e).map (p * ·) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Nat.mul_succ, List.range_add, List.filter_append, ih, List.range_succ,
      List.map_append]
    congr 1
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [List.range_succ_eq_map, List.map_cons, List.filter_cons, List.map_map]
    have : List.filter (fun k => decide (q + 1 ∣ k))
        (List.map ((fun x => (q + 1) * e + x) ∘ Nat.succ) (List.range q)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      simp only [List.mem_map, List.mem_range, Function.comp] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simp only [decide_eq_true_eq]
      intro hd
      have h2 : q + 1 ∣ y + 1 := by
        have := (Nat.dvd_add_right (Nat.dvd_mul_right (q + 1) e)).mp
          (by rw [Nat.succ_eq_add_one] at hd; exact hd)
        exact this
      have := Nat.le_of_dvd (by omega) h2
      omega
    simp [this, Nat.dvd_mul_right]

theorem symCount_eq {p : Nat} (hpL : p ∣ L) (hp0 : 0 < p)
    (hS : ∀ k, S L m k ↔ p ∣ k) : symCount L m = L / p := by
  unfold symCount
  have : (List.range L).filter (symAt L m) = (List.range L).filter (fun k => decide (p ∣ k)) := by
    apply List.filter_congr
    intro k _
    rw [Bool.eq_iff_iff, symAt_iff, hS, decide_eq_true_iff]
  rw [this]
  obtain ⟨e, he⟩ := hpL
  rw [he, filter_dvd_range p hp0 e, List.length_map, List.length_range,
    Nat.mul_div_cancel_left _ hp0]

theorem symCount_dvd (hL : 0 < L) (m : Nat) : symCount L m ∣ L := by
  obtain ⟨p, hp0, hpL, hS⟩ := period hL m
  rw [symCount_eq hpL hp0 hS]
  exact Nat.div_dvd_of_dvd hpL

/-! Repeated blocks. -/

def rep (a d : Nat) : Nat → Nat
  | 0 => 0
  | e + 1 => 2 ^ d * rep a d e + a

theorem rep_eq (a d e : Nat) : rep a d e = R d e * a := by
  induction e with
  | zero => simp [rep, R]
  | succ e ih => simp only [rep, R, ih, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]

theorem testBit_rep {a d : Nat} (ha : a < 2 ^ d) (e i : Nat) :
    (rep a d e).testBit i = (decide (i < d * e) && a.testBit (i % d)) := by
  induction e generalizing i with
  | zero => simp [rep]
  | succ e ih =>
    simp only [rep]
    rw [Nat.testBit_two_pow_mul_add _ ha]
    by_cases hi : i < d
    · simp only [hi, ↓reduceIte, Nat.mod_eq_of_lt hi]
      have : i < d * (e + 1) := by rw [Nat.mul_succ]; omega
      simp [this]
    · simp only [hi, ↓reduceIte]
      rw [ih]
      have h1 : (i - d) % d = i % d := by
        conv => rhs; rw [show i = (i - d) + d by omega]
        rw [Nat.add_mod_right]
      have h2 : (i - d < d * e) = (i < d * (e + 1)) := by
        rw [Nat.mul_succ]; apply propext; omega
      rw [h1]; simp only [h2]

theorem S_rep {a d : Nat} (ha : a < 2 ^ d) (e : Nat) : S (d * e) (rep a d e) d := by
  intro i hi
  rw [testBit_rep ha, testBit_rep ha, Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right d e),
    Nat.add_mod_right]
  have : (i + d) % (d * e) < d * e := Nat.mod_lt _ (by omega)
  simp [this, hi]

/-- An L-bit word with period d ∣ L is its low block repeated. -/
theorem eq_rep (hL : 0 < L) {d : Nat} (hd : 0 < d) (hdL : d ∣ L) (hm : m < 2 ^ L)
    (hS : S L m d) : m = rep (m % 2 ^ d) d (L / d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_rep (Nat.mod_lt _ (Nat.two_pow_pos d)), Nat.mul_div_cancel' hdL,
    Nat.testBit_mod_two_pow]
  by_cases hi : i < L
  · have h1 := S_mul hL hS (i / d) (i % d) (Nat.lt_of_lt_of_le (Nat.mod_lt _ hd) (Nat.le_of_dvd hL hdL))
    rw [Nat.mod_add_div, Nat.mod_eq_of_lt hi] at h1
    simp [hi, h1, Nat.mod_lt _ hd]
  · have : m.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hi, this]

/-! Binary length. -/

theorem log2_of_len {L m : Nat} (hL : 0 < L) (h1 : 2 ^ (L - 1) ≤ m) (h2 : m < 2 ^ L) :
    m.log2 + 1 = L := by
  have hm : m ≠ 0 := by have := Nat.two_pow_pos (L - 1); omega
  have := (Nat.log2_eq_iff (k := L - 1) hm).mpr ⟨h1, by rw [show L - 1 + 1 = L by omega]; exact h2⟩
  omega

theorem top_bit {L m : Nat} (hL : 0 < L) (h1 : 2 ^ (L - 1) ≤ m) (h2 : m < 2 ^ L) :
    m.testBit (L - 1) = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h3 : m / 2 ^ (L - 1) = 1 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · have : 2 ^ L = 2 * 2 ^ (L - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      omega
  simp [h3]

theorem len_of_bits {L m : Nat} (ht : m.testBit (L - 1) = true)
    (hb : ∀ i, L ≤ i → m.testBit i = false) : 2 ^ (L - 1) ≤ m ∧ m < 2 ^ L :=
  ⟨Nat.ge_two_pow_of_testBit ht, Nat.lt_pow_two_of_testBit m hb⟩

theorem A138904_eq (hL : 0 < L) (h1 : 2 ^ (L - 1) ≤ m) (h2 : m < 2 ^ L) :
    A138904 m = symCount L m := by
  unfold A138904; rw [log2_of_len hL h1 h2]

/-- First conjecture, part 1: a(m) divides the length. -/
theorem A138904_dvd (hL : 0 < L) (h1 : 2 ^ (L - 1) ≤ m) (h2 : m < 2 ^ L) : A138904 m ∣ L := by
  rw [A138904_eq hL h1 h2]; exact symCount_dvd hL m

end

/-- First conjecture, part 2: every divisor e of L is a(m) for some m of length L. -/
theorem A138904_values {L e : Nat} (hL : 0 < L) (he : e ∣ L) :
    ∃ m, 2 ^ (L - 1) ≤ m ∧ m < 2 ^ L ∧ A138904 m = e := by
  obtain ⟨q, hq⟩ : ∃ q, L = q * e := ⟨L / e, (Nat.div_mul_cancel he).symm⟩
  have hq0 : 0 < q := by
    apply Nat.pos_of_ne_zero; intro h; rw [h, Nat.zero_mul] at hq; omega
  have he0 : 0 < e := by
    apply Nat.pos_of_ne_zero; intro h; rw [h, Nat.mul_zero] at hq; omega
  have ha : 2 ^ (q - 1) < 2 ^ q := Nat.pow_lt_pow_right (by omega) (by omega)
  let m := rep (2 ^ (q - 1)) q e
  have hLqe : L = q * e := hq
  have hbit : ∀ i, m.testBit i = (decide (i < L) && decide (i % q = q - 1)) := by
    intro i
    rw [testBit_rep ha, Nat.testBit_two_pow, hLqe]
    simp [eq_comm]
  have hlen : 2 ^ (L - 1) ≤ m ∧ m < 2 ^ L := by
    apply len_of_bits
    · rw [hbit]
      have : (L - 1) % q = q - 1 := by
        rw [hLqe]
        have h3 : q * e - 1 = (q - 1) + q * (e - 1) := by
          rw [Nat.mul_sub, Nat.mul_one]
          have : q ≤ q * e := Nat.le_mul_of_pos_right q he0
          omega
        rw [h3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      simp [this]; omega
    · intro i hi; rw [hbit]; simp; omega
  refine ⟨m, hlen.1, hlen.2, ?_⟩
  rw [A138904_eq hL hlen.1 hlen.2]
  obtain ⟨p, hp0, hpL, hS⟩ := period hL m
  have hSq : S L m q := by rw [hLqe]; exact S_rep ha e
  have hpq : p ∣ q := (hS q).mp hSq
  have hp_eq : p = q := by
    apply Classical.byContradiction; intro hne
    have hplt : p < q := Nat.lt_of_le_of_ne (Nat.le_of_dvd hq0 hpq) hne
    have h := (hS p).mpr (Nat.dvd_refl p) (q - 1) (by rw [hLqe]; have := Nat.le_mul_of_pos_right q he0; omega)
    rw [hbit, hbit] at h
    have h4 : (q - 1 + p) % L % q = p - 1 := by
      rw [Nat.mod_mod_of_dvd _ (by rw [hLqe]; exact Nat.dvd_mul_right q e)]
      rw [show q - 1 + p = (p - 1) + q by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have h5 : (q - 1 + p) % L < L := Nat.mod_lt _ hL
    have h6 : (q - 1) % q = q - 1 := Nat.mod_eq_of_lt (by omega)
    have h7 : q - 1 < L := by rw [hLqe]; have := Nat.le_mul_of_pos_right q he0; omega
    have hR : (decide (q - 1 < L) && decide ((q - 1) % q = q - 1)) = true := by simp [h6, h7]
    rw [← h, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, h4] at hR
    omega
  rw [symCount_eq hpL hp0 hS, hp_eq, hLqe, Nat.mul_div_cancel_left _ hq0]

section
variable {L m : Nat}

theorem all_ones (hL : 0 < L) (h1 : 2 ^ (L - 1) ≤ m) (h2 : m < 2 ^ L) :
    S L m 1 ↔ m = 2 ^ L - 1 := by
  constructor
  · intro hS
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_two_pow_sub_one]
    by_cases hi : i < L
    · have h := S_mul hL hS (i + 1) (L - 1) (by omega)
      rw [Nat.one_mul, show L - 1 + (i + 1) = i + L by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hi, top_bit hL h1 h2] at h
      simp [h, hi]
    · have : m.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [hi, this]
  · rintro rfl i hi
    simp [hi, Nat.mod_lt _ hL]

/-- a(m) = L exactly for m = 2^L - 1. -/
theorem A138904_eq_length_iff (hL : 0 < L) (h1 : 2 ^ (L - 1) ≤ m) (h2 : m < 2 ^ L) :
    A138904 m = L ↔ m = 2 ^ L - 1 := by
  rw [A138904_eq hL h1 h2, ← all_ones hL h1 h2]
  obtain ⟨p, hp0, hpL, hS⟩ := period hL m
  rw [symCount_eq hpL hp0 hS, hS]
  constructor
  · intro h
    have : p = 1 := by
      apply Classical.byContradiction; intro hne
      have := Nat.div_lt_self hL (show 1 < p by omega); omega
    rw [this]; exact Nat.dvd_refl 1
  · intro h; rw [Nat.eq_one_of_dvd_one h, Nat.div_one]

/-- For a prime d ∣ L with d < L: a(m) = L/d iff m = R·a, 2^(d-1) ≤ a < 2^d - 1. -/
theorem A138904_prime_block {d : Nat} (hd : IsPrime d) (hdL : d ∣ L) (hdlt : d < L)
    (h1 : 2 ^ (L - 1) ≤ m) (h2 : m < 2 ^ L) :
    A138904 m = L / d ↔ ∃ a, 2 ^ (d - 1) ≤ a ∧ a < 2 ^ d - 1 ∧ m = R d (L / d) * a := by
  have hL : 0 < L := by omega
  have hd0 : 0 < d := by have := hd.1; omega
  have hLd : d * (L / d) = L := Nat.mul_div_cancel' hdL
  rw [A138904_eq hL h1 h2]
  obtain ⟨p, hp0, hpL, hS⟩ := period hL m
  rw [symCount_eq hpL hp0 hS]
  constructor
  · intro h
    have hpd : p = d := by
      rw [← Nat.div_div_self hpL (by omega), h, Nat.div_div_self hdL (by omega)]
    have hSd : S L m d := (hS d).mpr (by rw [hpd]; exact Nat.dvd_refl d)
    refine ⟨m % 2 ^ d, ?_, ?_, ?_⟩
    · apply Nat.ge_two_pow_of_testBit
      rw [Nat.testBit_mod_two_pow]
      have h3 := S_mul hL hSd (L / d - 1) (d - 1) (by omega)
      rw [show d - 1 + d * (L / d - 1) = L - 1 by
            rw [Nat.mul_sub, Nat.mul_one, hLd]
            have : d ≤ L := Nat.le_of_lt hdlt
            omega,
          Nat.mod_eq_of_lt (by omega), top_bit hL h1 h2] at h3
      simp [← h3]; omega
    · have hlt : m % 2 ^ d < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)
      apply Nat.lt_of_le_of_ne (by omega)
      intro heq
      have hm : m = rep (m % 2 ^ d) d (L / d) := eq_rep hL hd0 hdL h2 hSd
      have h1' : S L m 1 := by
        rw [hm, heq]
        intro i hi
        rw [testBit_rep (by omega), testBit_rep (by omega), hLd]
        simp [Nat.mod_lt _ hd0, Nat.mod_lt _ hL, hi]
      have := (hS 1).mp h1'
      have := Nat.eq_one_of_dvd_one this
      have := hd.1
      omega
    · rw [← rep_eq]; exact eq_rep hL hd0 hdL h2 hSd
  · rintro ⟨a, ha1, ha2, rfl⟩
    have ha : a < 2 ^ d := by omega
    rw [← rep_eq] at h1 h2 hS
    have hSd : S L (rep a d (L / d)) d := by
      have := S_rep (a := a) ha (L / d); rw [hLd] at this; exact this
    have hpd : p ∣ d := (hS d).mp hSd
    rcases hd.2 p hpd with hp1 | hp1
    · exfalso
      have hS1 : S L (rep a d (L / d)) 1 := (hS 1).mpr (by rw [hp1]; exact Nat.dvd_refl 1)
      have hall := (all_ones hL h1 h2).mp hS1
      have hbits : ∀ j, j < d → a.testBit j = true := by
        intro j hj
        have : (rep a d (L / d)).testBit j = (2 ^ L - 1).testBit j := by rw [hall]
        rw [testBit_rep ha, Nat.testBit_two_pow_sub_one, hLd, Nat.mod_eq_of_lt hj] at this
        simp [show j < L by omega] at this
        exact this
      have : a = 2 ^ d - 1 := by
        apply Nat.eq_of_testBit_eq
        intro j
        rw [Nat.testBit_two_pow_sub_one]
        by_cases hj : j < d
        · simp [hj, hbits j hj]
        · have hj' : d ≤ j := by omega
          simp [hj, Nat.testBit_lt_two_pow (i := j) (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hj'))]
      omega
    · rw [hp1]

/-- Under the hypothesis of the second conjecture every proper divisor > 1 of L is prime. -/
theorem proper_prime (hcop : ∀ d₁ d₂, d₁ ∣ L → d₂ ∣ L → 1 < d₁ → d₁ < L → 1 < d₂ → d₂ < L →
      d₁ ≠ d₂ → Nat.gcd d₁ d₂ = 1)
    {d : Nat} (hdL : d ∣ L) (h1 : 1 < d) (h2 : d < L) : IsPrime d := by
  refine ⟨h1, fun k hk => ?_⟩
  apply Classical.byContradiction; intro hne
  have hk0 : 0 < k := Nat.pos_of_dvd_of_pos hk (by omega)
  have hkd : k ≤ d := Nat.le_of_dvd (by omega) hk
  have hg := hcop k d (Nat.dvd_trans hk hdL) hdL (by omega) (by omega) h1 h2 (by omega)
  rw [Nat.gcd_eq_left hk] at hg
  omega

/-- Second conjecture, last part: if the divisors of L strictly between 1 and L are
pairwise coprime, an m of length L other than 2^L - 1 and the blocks R·a has a(m) = 1. -/
theorem A138904_rest
    (hcop : ∀ d₁ d₂, d₁ ∣ L → d₂ ∣ L → 1 < d₁ → d₁ < L → 1 < d₂ → d₂ < L →
      d₁ ≠ d₂ → Nat.gcd d₁ d₂ = 1)
    (hL : 0 < L) (h1 : 2 ^ (L - 1) ≤ m) (h2 : m < 2 ^ L) (hne : m ≠ 2 ^ L - 1)
    (hblk : ∀ d, d ∣ L → 1 < d → d < L →
      ¬ ∃ a, 2 ^ (d - 1) ≤ a ∧ a < 2 ^ d - 1 ∧ m = R d (L / d) * a) :
    A138904 m = 1 := by
  obtain ⟨p, hp0, hpL, hS⟩ := period hL m
  have hc : A138904 m = L / p := by rw [A138904_eq hL h1 h2]; exact symCount_eq hpL hp0 hS
  have hpleL : p ≤ L := Nat.le_of_dvd hL hpL
  by_cases hp1 : p = 1
  · exfalso; apply hne
    rw [← A138904_eq_length_iff hL h1 h2, hc, hp1, Nat.div_one]
  by_cases hpL' : p = L
  · rw [hc, hpL', Nat.div_self hL]
  exfalso
  have hpr := proper_prime hcop hpL (by omega) (by omega)
  exact hblk p hpL (by omega) (by omega)
    ((A138904_prime_block hpr hpL (by omega) h1 h2).mp hc)

end

/-- Spot check against the listed terms a(0..20). -/
theorem A138904_terms :
    (List.range 21).map A138904 = [1,1,1,2,1,1,1,3,1,1,2,1,1,1,1,4,1,1,1,1,1] := by decide
