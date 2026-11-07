/-
OEIS A077739 and A077740 (Mathlib): a(n) = 0 iff n is 11, 17 or 19.

A077739(n) is the smallest multiple of n beginning and ending in n and having digit sum n,
or 0 if no such number exists; A077740(n) = A077739(n)/n. Both entries conjecture that
a(n) = 0 iff n is 11, 17 or 19.

Checked here:
* `A077739_Good n N` encodes the definition: n ∣ N, the decimal string of N begins and ends with that
  of n, and the digit sum of N is n. `Nat.digits` is little-endian, so "ends with n" is the list
  prefix relation `<+:` and "begins with n" the list suffix relation `<:+`.
* `A077739_eq_zero_iff`, `A077740_eq_zero_iff`: for n ≥ 1, a(n) = 0 ↔ n = 11 ∨ n = 17 ∨ n = 19.
* Non-existence for 11 (alternating digit sum is odd and of size at most 9), 17 (the A077739_middle
  digits sum to 1, so 17 would divide a power of 10) and 19 (digit sum at least 20).
* Existence for n ≥ 63 by an explicit construction (`A077739_construct`), and explicit witnesses
  (checked by `norm_num`) for the other n ≤ 62.
Not checked: that the witnesses are the least ones (the OEIS values); only existence matters.
-/
import Mathlib
import OpenProblemsLib.Digits10


open Nat OpenProblemsLib.Digits10

/-- N is a multiple of n whose decimal string begins and ends with that of n and whose digit
sum is n. -/
def A077739_Good (n N : ℕ) : Prop :=
  n ∣ N ∧ digits 10 n <+: digits 10 N ∧ digits 10 n <:+ digits 10 N ∧ (digits 10 N).sum = n

open Classical in
/-- A077739(n): the least N with `A077739_Good n N`, or 0 if there is none. -/
noncomputable def A077739 (n : ℕ) : ℕ := if h : ∃ N, A077739_Good n N then Nat.find h else 0

/-- A077740(n) = A077739(n)/n. -/
noncomputable def A077740 (n : ℕ) : ℕ := A077739 n / n

/-- Horner evaluation with blocks of S digits. -/
def A077739_H (S : ℕ) : List ℕ → ℕ
  | [] => 0
  | b :: l => b + 10 ^ S * A077739_H S l

theorem A077739_H_ds (S : ℕ) : ∀ l : List ℕ, (∀ b ∈ l, b < 10 ^ S ∧ (digits 10 b).sum = 1) → (digits 10 (A077739_H S l)).sum = l.length
  | [], _ => by simp [A077739_H]
  | b :: l, h => by
    simp only [A077739_H, List.length_cons]
    rw [digitSum_add S b _ (h b (by simp)).1, (h b (by simp)).2,
      A077739_H_ds S l (fun c hc => h c (by simp [hc]))]
    ring

theorem A077739_H_mod (n i S : ℕ) (hS : 10 ^ (i + S) ≡ 10 ^ i [MOD n]) :
    ∀ l : List ℕ, 10 ^ i * A077739_H S l ≡ 10 ^ i * l.sum [MOD n]
  | [] => by simp [A077739_H]; exact Nat.ModEq.refl 0
  | b :: l => by
    simp only [A077739_H, List.sum_cons]
    have e1 : 10 ^ i * (b + 10 ^ S * A077739_H S l) = 10 ^ i * b + 10 ^ (i + S) * A077739_H S l := by ring
    have e2 : 10 ^ i * (b + l.sum) = 10 ^ i * b + 10 ^ i * l.sum := by ring
    rw [e1, e2]
    exact Nat.ModEq.add_left _ ((Nat.ModEq.mul_right _ hS).trans (A077739_H_mod n i S hS l))

theorem A077739_coprime_part (n i : ℕ) (hn : 0 < n) : ∃ q, 0 < q ∧ q ∣ n ∧ n ∣ 10 ^ i * q := by
  refine ⟨n / Nat.gcd n (10 ^ i),
    Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_left _ _)) (Nat.gcd_pos_of_pos_left _ hn),
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _), ?_⟩
  obtain ⟨e, he⟩ := Nat.gcd_dvd_right n (10 ^ i)
  refine ⟨e, ?_⟩
  calc 10 ^ i * (n / Nat.gcd n (10 ^ i))
      = Nat.gcd n (10 ^ i) * e * (n / Nat.gcd n (10 ^ i)) := by rw [← he]
    _ = (Nat.gcd n (10 ^ i) * (n / Nat.gcd n (10 ^ i))) * e := by ring
    _ = n * e := by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]

/-- For n ≥ 63 there is a multiple of n with digit sum n - 2·(digit sum of n). -/
theorem A077739_middle (n : ℕ) (hn : 63 ≤ n) : ∃ M, n ∣ M ∧ (digits 10 M).sum = n - 2 * (digits 10 n).sum := by
  obtain ⟨i, P, hP, hper⟩ := pow_period n (by omega)
  have hS : 10 ^ (i + 3 * P) ≡ 10 ^ i [MOD n] := by
    have := pow_period_mul n i P hper 0 3
    rw [Nat.add_zero, show P * 3 = 3 * P by ring] at this
    exact this
  obtain ⟨q, hq0, hqn, hnq⟩ := A077739_coprime_part n i (by omega)
  have hqle : q ≤ n := Nat.le_of_dvd (by omega) hqn
  obtain ⟨w, hw⟩ := hqn
  have hsn := digitSum_le n
  have h9 : n % 9 = (digits 10 n).sum % 9 := Nat.modEq_nine_digits_sum n
  obtain ⟨s, hs⟩ : ∃ s, s = (digits 10 n).sum := ⟨_, rfl⟩
  rw [← hs] at hsn h9 ⊢
  obtain ⟨r, hr⟩ : ∃ r, r = n - 2 * s := ⟨_, rfl⟩
  rw [← hr]
  obtain ⟨m0, hm0⟩ : ∃ m0, m0 = 9 - w % 9 := ⟨_, rfl⟩
  have hA : (q * m0 + n) % 9 = 0 := by
    have : 9 - w % 9 + w = 9 * (w / 9 + 1) := by omega
    have e : q * m0 + n = 9 * (q * (w / 9 + 1)) := by
      rw [hw, hm0, ← mul_add, this]; ring
    rw [e]; simp
  obtain ⟨k, hk⟩ : ∃ k, k = r / (9 * q) + 1 := ⟨_, rfl⟩
  have hk1 : r < 9 * (q * k) := by
    rw [← mul_assoc, hk]; exact Nat.lt_mul_div_succ r (by positivity)
  have hk2 : 9 * (q * k) ≤ r + 9 * q := by
    have := Nat.mul_div_le r (9 * q)
    rw [← mul_assoc, hk, mul_add, mul_one]; omega
  have hm0le : q * m0 ≤ 9 * q := by
    have : m0 ≤ 9 := by omega
    nlinarith
  have hVq : q * m0 + 9 * (q * k) = q * (m0 + 9 * k) := by ring
  generalize hX : q * m0 = X at hA hm0le hVq
  generalize hZ : q * k = Z at hk1 hk2 hVq
  obtain ⟨y, hy⟩ : ∃ y, X + 9 * Z = r + 9 * y := ⟨(X + 9 * Z - r) / 9, by omega⟩
  have hy2 : y ≤ 2 * n := by omega
  have hsum : (List.replicate (r - y % 11 - y / 11) 1 ++ List.replicate (y % 11) 10 ++
      List.replicate (y / 11) 100).sum = X + 9 * Z := by
    simp only [List.sum_append, List.sum_replicate, smul_eq_mul]
    omega
  have hlen : (List.replicate (r - y % 11 - y / 11) 1 ++ List.replicate (y % 11) 10 ++
      List.replicate (y / 11) 100).length = r := by
    simp only [List.length_append, List.length_replicate]
    omega
  have h1000 : 1000 ≤ 10 ^ (3 * P) := by
    calc 1000 = 10 ^ 3 := by norm_num
      _ ≤ 10 ^ (3 * P) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd1 : (digits 10 1).sum = 1 := by norm_num
  have hd10 : (digits 10 10).sum = 1 := by norm_num
  have hd100 : (digits 10 100).sum = 1 := by norm_num
  have hb : ∀ b ∈ (List.replicate (r - y % 11 - y / 11) 1 ++ List.replicate (y % 11) 10 ++
      List.replicate (y / 11) 100), b < 10 ^ (3 * P) ∧ (digits 10 b).sum = 1 := by
    intro b hb
    simp only [List.mem_append, List.mem_replicate] at hb
    rcases hb with (⟨-, hb⟩ | ⟨-, hb⟩) | ⟨-, hb⟩ <;> subst hb
    · exact ⟨by omega, hd1⟩
    · exact ⟨by omega, hd10⟩
    · exact ⟨by omega, hd100⟩
  refine ⟨10 ^ i * A077739_H (3 * P) (List.replicate (r - y % 11 - y / 11) 1 ++
      List.replicate (y % 11) 10 ++ List.replicate (y / 11) 100), ?_, ?_⟩
  · have h1 := A077739_H_mod n i (3 * P) hS (List.replicate (r - y % 11 - y / 11) 1 ++
      List.replicate (y % 11) 10 ++ List.replicate (y / 11) 100)
    rw [hsum, hVq] at h1
    have h2 : n ∣ 10 ^ i * (q * (m0 + 9 * k)) := by
      rw [← mul_assoc]; exact Dvd.dvd.mul_right hnq _
    exact (Nat.modEq_zero_iff_dvd.mp (h1.trans (Nat.modEq_zero_iff_dvd.mpr h2)))
  · have := digitSum_add i 0 (A077739_H (3 * P) (List.replicate (r - y % 11 - y / 11) 1 ++
      List.replicate (y % 11) 10 ++ List.replicate (y / 11) 100)) (by positivity)
    rw [Nat.zero_add] at this
    rw [this, A077739_H_ds (3 * P) _ hb, hlen]
    simp

theorem A077739_construct (n : ℕ) (hn : 63 ≤ n) : ∃ N, A077739_Good n N := by
  obtain ⟨M, hM, hdsM⟩ := A077739_middle n hn
  have hsn := digitSum_le n
  have hnD : n < 10 ^ (digits 10 n).length := Nat.lt_base_pow_length_digits (by norm_num)
  have hMK : M < 10 ^ M := Nat.lt_pow_self (by norm_num)
  refine ⟨n + 10 ^ (digits 10 n).length * (M + 10 ^ M * n), ?_, ?_, ?_, ?_⟩
  · exact dvd_add dvd_rfl (Dvd.dvd.mul_left (dvd_add hM (Dvd.intro_left _ rfl)) _)
  · rw [← Nat.digits_append_digits (by norm_num)]
    exact List.prefix_append _ _
  · have hX : n + 10 ^ (digits 10 n).length * M < 10 ^ ((digits 10 n).length + M) := by
      rw [pow_add]
      have : n + 10 ^ (digits 10 n).length * M < 10 ^ (digits 10 n).length * (M + 1) := by
        rw [mul_add, mul_one]; omega
      calc _ < _ := this
        _ ≤ _ := Nat.mul_le_mul_left _ hMK
    have hlenX := (Nat.digits_length_le_iff (by norm_num) _).mpr hX
    have h := Nat.digits_append_zeroes_append_digits (b := 10)
      (k := (digits 10 n).length + M - (digits 10 (n + 10 ^ (digits 10 n).length * M)).length)
      (m := n) (n := n + 10 ^ (digits 10 n).length * M) (by norm_num) (by omega)
    rw [show (digits 10 (n + 10 ^ (digits 10 n).length * M)).length +
        ((digits 10 n).length + M - (digits 10 (n + 10 ^ (digits 10 n).length * M)).length) =
        (digits 10 n).length + M by omega] at h
    have e : n + 10 ^ (digits 10 n).length * (M + 10 ^ M * n) =
        n + 10 ^ (digits 10 n).length * M + 10 ^ ((digits 10 n).length + M) * n := by
      rw [pow_add]; ring
    rw [e, ← h]
    exact List.suffix_append _ _
  · have e1 := digitSum_add _ n (M + 10 ^ M * n) hnD
    have e2 := digitSum_add M M n hMK
    show (digits 10 (n + 10 ^ (digits 10 n).length * (M + 10 ^ M * n))).sum = n
    rw [e1, e2, hdsM]
    omega

/-- Two-digit pattern at both ends: either they coincide or they do not overlap. -/
theorem A077739_split2 {d1 d2 : ℕ} {A B : List ℕ} (h : B ++ [d1, d2] = [d1, d2] ++ A) (hne : d1 ≠ d2) :
    A = [] ∨ ∃ C, A = C ++ [d1, d2] := by
  rcases A with _ | ⟨x, _ | ⟨y, A⟩⟩
  · exact Or.inl rfl
  · exfalso
    have hl := congrArg List.length h
    simp at hl
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hl
    have h' := congrArg (fun L : List ℕ => L[1]?) h
    simp at h'
    exact hne h'
  · right
    rcases List.append_eq_append_iff.mp h with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
    · have hl := congrArg List.length h2
      simp at hl
      have has : as = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst has
      exact ⟨[], by simpa using h2.symm⟩
    · exact ⟨bs, h2⟩

theorem A077739_not_good_19 (N : ℕ) : ¬ A077739_Good 19 N := by
  rintro ⟨-, ⟨A, hA⟩, ⟨B, hB⟩, hs⟩
  have h19 : digits 10 19 = [9, 1] := by norm_num
  rw [h19] at hA hB
  rw [← hA] at hs hB
  rcases A077739_split2 hB (by norm_num) with rfl | ⟨C, rfl⟩
  · simp at hs
  · simp [List.sum_append] at hs
    omega

theorem A077739_zero_sum_ofDigits : ∀ C : List ℕ, C.sum = 0 → ofDigits 10 C = 0
  | [], _ => by simp
  | d :: C, h => by
    simp only [List.sum_cons] at h
    rw [Nat.ofDigits_cons, A077739_zero_sum_ofDigits C (by omega)]
    omega

theorem A077739_one_sum_ofDigits : ∀ C : List ℕ, C.sum = 1 → ∃ j, ofDigits 10 C = 10 ^ j
  | [], h => by simp at h
  | d :: C, h => by
    simp only [List.sum_cons] at h
    rw [Nat.ofDigits_cons]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · obtain ⟨j, hj⟩ := A077739_one_sum_ofDigits C (by omega)
      exact ⟨j + 1, by rw [hj, pow_succ]; ring⟩
    · exact ⟨0, by rw [A077739_zero_sum_ofDigits C (by omega)]; simp; omega⟩

theorem A077739_not_good_17 (N : ℕ) : ¬ A077739_Good 17 N := by
  rintro ⟨hdvd, ⟨A, hA⟩, ⟨B, hB⟩, hs⟩
  have h17 : digits 10 17 = [7, 1] := by norm_num
  rw [h17] at hA hB
  rw [← hA] at hs hB
  rcases A077739_split2 hB (by norm_num) with rfl | ⟨C, rfl⟩
  · simp at hs
  · simp [List.sum_append] at hs
    have hN : N = ofDigits 10 ([7, 1] ++ (C ++ [7, 1])) := by rw [hA, Nat.ofDigits_digits]
    simp only [Nat.ofDigits_append] at hN
    have h71 : ofDigits 10 [7, 1] = 17 := by norm_num [Nat.ofDigits]
    rw [h71] at hN
    simp only [List.length_cons, List.length_nil] at hN
    obtain ⟨j, hj⟩ := A077739_one_sum_ofDigits C (by omega)
    rw [hj] at hN
    have e : N = 17 * (1 + 10 ^ 2 * 10 ^ C.length) + 100 * 10 ^ j := by rw [hN]; ring
    rw [e] at hdvd
    have h1 : 17 ∣ 100 * 10 ^ j := (Nat.dvd_add_right (dvd_mul_right 17 _)).mp hdvd
    have h2 : 17 ∣ 10 ^ (j + 2) := by
      rw [pow_add]; rw [show (100 : ℕ) = 10 ^ 2 by norm_num] at h1; rw [mul_comm]; exact h1
    have := (Nat.prime_iff.mp (by norm_num : Nat.Prime 17)).dvd_of_dvd_pow h2
    norm_num at this

theorem A077739_alt_bound : ∀ l : List ℕ,
    -(l.sum : ℤ) ≤ (l.map (fun n : ℕ => (n : ℤ))).alternatingSum ∧
    (l.map (fun n : ℕ => (n : ℤ))).alternatingSum ≤ l.sum ∧
    ((l.sum : ℤ) - (l.map (fun n : ℕ => (n : ℤ))).alternatingSum) % 2 = 0
  | [] => by simp
  | [a] => by simp [List.alternatingSum]
  | a :: b :: t => by
    have ih := A077739_alt_bound t
    simp only [List.map_cons, List.alternatingSum, List.sum_cons, Nat.cast_add]
    omega

theorem A077739_not_good_11 (N : ℕ) : ¬ A077739_Good 11 N := by
  rintro ⟨hdvd, ⟨A, hA⟩, -, hs⟩
  have h11 : digits 10 11 = [1, 1] := by norm_num
  rw [h11] at hA
  rw [← hA] at hs
  have hd := Nat.eleven_dvd_iff.mp hdvd
  rw [← hA] at hd
  simp only [List.cons_append, List.nil_append, List.map_cons, List.alternatingSum] at hd
  simp only [List.cons_append, List.nil_append, List.sum_cons] at hs
  obtain ⟨c, hc⟩ := hd
  have hb := A077739_alt_bound A
  have hA9 : (A.sum : ℤ) = 9 := by omega
  push_cast at hc
  omega

theorem A077739_exists_good_iff (n : ℕ) (hn : 1 ≤ n) :
    (∃ N, A077739_Good n N) ↔ ¬ (n = 11 ∨ n = 17 ∨ n = 19) := by
  constructor
  · rintro ⟨N, hN⟩ (rfl | rfl | rfl)
    · exact A077739_not_good_11 N hN
    · exact A077739_not_good_17 N hN
    · exact A077739_not_good_19 N hN
  · intro h
    by_cases h63 : 63 ≤ n
    · exact A077739_construct n h63
    interval_cases n
    · exact ⟨1, dvd_rfl, List.prefix_refl _, List.suffix_refl _, by norm_num⟩
    · exact ⟨2, dvd_rfl, List.prefix_refl _, List.suffix_refl _, by norm_num⟩
    · exact ⟨3, dvd_rfl, List.prefix_refl _, List.suffix_refl _, by norm_num⟩
    · exact ⟨4, dvd_rfl, List.prefix_refl _, List.suffix_refl _, by norm_num⟩
    · exact ⟨5, dvd_rfl, List.prefix_refl _, List.suffix_refl _, by norm_num⟩
    · exact ⟨6, dvd_rfl, List.prefix_refl _, List.suffix_refl _, by norm_num⟩
    · exact ⟨7, dvd_rfl, List.prefix_refl _, List.suffix_refl _, by norm_num⟩
    · exact ⟨8, dvd_rfl, List.prefix_refl _, List.suffix_refl _, by norm_num⟩
    · exact ⟨9, dvd_rfl, List.prefix_refl _, List.suffix_refl _, by norm_num⟩
    · exact ⟨10810, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact absurd (by norm_num) h
    · exact ⟨12612, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨1310413, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨1411214, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨15315, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨162016, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact absurd (by norm_num) h
    · exact ⟨1818, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact absurd (by norm_num) h
    · exact ⟨207920, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨2116821, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨227722, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨2318423, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨244824, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨252925, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨269126, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨272727, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨283528, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨2923229, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨3069930, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨31275931, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨3268832, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨3375933, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨3457834, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨3546935, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨369936, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨3729637, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨3847538, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨397839, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨40699840, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨411877841, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨42499842, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨43498843, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨44559944, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨4599945, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨4698946, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨4779947, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨4888848, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨49259749, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨504999950, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨516879951, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨525879952, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨532999853, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨541989954, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨555399955, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨56989856, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨571789857, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨58698958, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨59896859, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨6039999960, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨6159889861, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩
    · exact ⟨6257997962, by refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩; norm_num; decide⟩

theorem A077739_good_pos {n N : ℕ} (hn : 1 ≤ n) (h : A077739_Good n N) : n ≤ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := h.2.2.2
    simp at this
    omega
  · exact Nat.le_of_dvd hN h.1

open Classical in
/-- Main theorem for A077739: for n ≥ 1, a(n) = 0 iff n ∈ {11, 17, 19}. -/
theorem A077739_eq_zero_iff (n : ℕ) (hn : 1 ≤ n) :
    A077739 n = 0 ↔ (n = 11 ∨ n = 17 ∨ n = 19) := by
  unfold A077739
  split_ifs with h
  · have hpos := A077739_good_pos hn (Nat.find_spec h)
    constructor
    · intro h0; omega
    · intro h'; exact absurd h' ((A077739_exists_good_iff n hn).mp h)
  · constructor
    · intro _
      by_contra h'
      exact h ((A077739_exists_good_iff n hn).mpr h')
    · intro _; rfl

open Classical in
/-- Main theorem for A077740 = A077739/n: for n ≥ 1, a(n) = 0 iff n ∈ {11, 17, 19}. -/
theorem A077740_eq_zero_iff (n : ℕ) (hn : 1 ≤ n) :
    A077740 n = 0 ↔ (n = 11 ∨ n = 17 ∨ n = 19) := by
  rw [← A077739_eq_zero_iff n hn]
  unfold A077740 A077739
  split_ifs with h
  · have hpos := A077739_good_pos hn (Nat.find_spec h)
    have h1 := Nat.div_pos hpos (by omega)
    constructor
    · intro h0; omega
    · intro h0; omega
  · simp

