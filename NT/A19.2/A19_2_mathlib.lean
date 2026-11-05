import Mathlib

/-
NT-A19.2 (Mathlib). Guy A19, Erdős: are there infinitely many n such that n - 2^k is
squarefree for every k ≥ 0 with 2^k < n?  (OEIS A091155.)

Main theorem `A19_2_main`:
  Set.Infinite {n : ℕ | ∀ k : ℕ, 2 ^ k < n → Squarefree (n - 2 ^ k)}.
Quantitative step `A19_exists`: for every s ≥ 20 there is such an n with s < n.

Proof (CRT + union bound, see README). Fix s ≥ 20, y = 2310 s, L = 4851 s, K = 2L,
x = 2^K. Let R be the product of the odd primes ≤ y and M = 4R. Candidates are
n = c + M j (j < x/M - 1) with c ≡ 3 (mod 4) and R ∣ c, so all candidates are ≤ x.
* 4 never divides n - 2^k (n ≡ 3 mod 4), and an odd prime p ≤ y divides n but not 2^k.
* So a bad candidate has p^2 ∣ n - 2^k with k < K and p a prime in (y, 2^L]. For fixed
  (k, p) such candidates are pairwise congruent mod M p^2, hence at most x/(M p^2) + 1.
* Σ_{p prime in (y, 2^L]} 1/p^2 ≤ Σ_{m > 2310 s, gcd(m, 2310) = 1} 1/m^2
  ≤ (φ(2310)/2310^2) Σ_{j ≥ s} 1/j^2 ≤ 480/(2310^2 (s-1)) (blocks of length 2310 and
  telescoping). With K = 9702 s this makes K Σ 1/p^2 ≤ 23/25.
* If every candidate were bad: x/M - 2 ≤ K (x/M · 23/(25K) + 2^L), and x/M ≥ 2^(5082 s - 2),
  which is false. So some candidate is good, and it is ≥ R > 1155 s (Bertrand).

Checked by Lean: everything above, with Mathlib's `primorial_le_four_pow`,
`Nat.filter_coprime_Ico_eq_totient`, Bertrand's postulate, `Nat.squarefree_iff_prime_squarefree`.
Not checked by Lean: nothing (the README and certificate scripts are human/numeric
companions; the A091155 term list is checked in Python only, it is not used here).
-/

open Finset


/-- Product of the odd primes ≤ y. -/
def A19_oddPrimorial (y : ℕ) : ℕ :=
  ∏ p ∈ (range (y + 1)).filter (fun p => p.Prime ∧ p ≠ 2), p

/-! ### A set of numbers ≤ x that are pairwise congruent mod L has at most x/L + 1 elements -/

theorem A19_card_le_of_modEq (s : Finset ℕ) (x L : ℕ)
    (hx : ∀ n ∈ s, n ≤ x) (hc : ∀ a ∈ s, ∀ b ∈ s, a ≡ b [MOD L]) :
    s.card ≤ x / L + 1 := by
  have h : s.card ≤ (range (x / L + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun n => n / L)
    · intro n hn
      exact Finset.mem_coe.2 (Finset.mem_range.2
        (Nat.lt_succ_of_le (Nat.div_le_div_right (hx n (Finset.mem_coe.1 hn)))))
    · intro a ha b hb hab
      have h1 : a % L = b % L := hc a (Finset.mem_coe.1 ha) b (Finset.mem_coe.1 hb)
      have h2 : a / L = b / L := hab
      rw [← Nat.div_add_mod a L, ← Nat.div_add_mod b L, h1, h2]
  simpa using h

/-! ### Telescoping: Σ_{s ≤ j < s+N} 1/j^2 ≤ 1/(s-1) - 1/(s+N-1) -/

theorem A19_tele (s : ℕ) (hs : 2 ≤ s) (N : ℕ) :
    ∑ j ∈ Ico s (s + N), (1 : ℝ) / (j : ℝ) ^ 2
      ≤ 1 / ((s : ℝ) - 1) - 1 / ((s : ℝ) + N - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show s + (N + 1) = (s + N) + 1 by ring, Finset.sum_Ico_succ_top (by omega : s ≤ s + N)]
    have h2 : (2 : ℝ) ≤ s := by exact_mod_cast hs
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have key : (1 : ℝ) / ((s + N : ℕ) : ℝ) ^ 2
        ≤ 1 / ((s : ℝ) + N - 1) - 1 / ((s : ℝ) + ((N + 1 : ℕ) : ℝ) - 1) := by
      push_cast
      rw [show (s : ℝ) + (N + 1) - 1 = s + N by ring]
      rw [div_sub_div _ _ (by linarith) (by linarith),
        div_le_div_iff₀ (by positivity) (by nlinarith)]
      nlinarith
    linarith

/-! ### φ(2310) = 480 -/

theorem A19_totient_2310 : Nat.totient 2310 = 480 := by
  rw [show (2310 : ℕ) = 2 * 3 * 5 * 7 * 11 by norm_num,
    Nat.totient_mul (show Nat.Coprime (2 * 3 * 5 * 7) 11 by norm_num),
    Nat.totient_mul (show Nat.Coprime (2 * 3 * 5) 7 by norm_num),
    Nat.totient_mul (show Nat.Coprime (2 * 3) 5 by norm_num),
    Nat.totient_mul (show Nat.Coprime 2 3 by norm_num),
    Nat.totient_prime (by norm_num : Nat.Prime 2), Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 5), Nat.totient_prime (by norm_num : Nat.Prime 7),
    Nat.totient_prime (by norm_num : Nat.Prime 11)]

/-! ### Σ_{m > 2310 s, gcd(m, 2310) = 1} 1/m^2 ≤ 480/2310^2 · 1/(s-1) -/

theorem A19_sum_coprime (s B : ℕ) (hs : 2 ≤ s) :
    ∑ m ∈ (Ioc (2310 * s) B).filter (fun m => Nat.Coprime 2310 m), (1 : ℝ) / (m : ℝ) ^ 2
      ≤ 480 / 2310 ^ 2 * (1 / ((s : ℝ) - 1)) := by
  set A := (Ioc (2310 * s) B).filter (fun m => Nat.Coprime 2310 m) with hA
  have hmaps : ∀ m ∈ A, m / 2310 ∈ Ico s (s + B) := by
    intro m hm
    simp only [hA, mem_filter, mem_Ioc] at hm
    simp only [mem_Ico]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ j ∈ Ico s (s + B),
      ∑ m ∈ A.filter (fun m => m / 2310 = j), (1 : ℝ) / (m : ℝ) ^ 2
        ≤ 480 / 2310 ^ 2 * (1 / (j : ℝ) ^ 2) := by
    intro j hj
    have hj1 : 1 ≤ j := by simp only [mem_Ico] at hj; omega
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
    have hcard : (A.filter (fun m => m / 2310 = j)).card ≤ 480 := by
      rw [← A19_totient_2310, ← Nat.filter_coprime_Ico_eq_totient 2310 (2310 * j)]
      apply Finset.card_le_card
      intro m hm
      simp only [hA, mem_filter, mem_Ioc, mem_Ico] at hm ⊢
      refine ⟨⟨?_, ?_⟩, hm.1.2⟩ <;> omega
    calc ∑ m ∈ A.filter (fun m => m / 2310 = j), (1 : ℝ) / (m : ℝ) ^ 2
        ≤ ∑ m ∈ A.filter (fun m => m / 2310 = j), (1 : ℝ) / ((2310 : ℝ) * j) ^ 2 := by
          apply Finset.sum_le_sum
          intro m hm
          simp only [mem_filter] at hm
          have h1 : 2310 * j ≤ m := by omega
          have h2 : (2310 : ℝ) * j ≤ m := by exact_mod_cast h1
          have h3 : (0 : ℝ) < 2310 * j := mul_pos (by norm_num) hjpos
          exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ h3.le h2 2)
      _ = ((A.filter (fun m => m / 2310 = j)).card : ℝ) * (1 / ((2310 : ℝ) * j) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 480 * (1 / ((2310 : ℝ) * j) ^ 2) := by
          gcongr
          exact_mod_cast hcard
      _ = 480 / 2310 ^ 2 * (1 / (j : ℝ) ^ 2) := by
          field_simp
  have h2 : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hv : (0 : ℝ) ≤ 1 / ((s : ℝ) + B - 1) := div_nonneg zero_le_one (by linarith)
  have hc : (0 : ℝ) ≤ 480 / 2310 ^ 2 := by norm_num
  calc _ ≤ ∑ j ∈ Ico s (s + B), (480 / 2310 ^ 2 : ℝ) * (1 / (j : ℝ) ^ 2) :=
        Finset.sum_le_sum hfib
    _ = 480 / 2310 ^ 2 * ∑ j ∈ Ico s (s + B), (1 : ℝ) / (j : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ 480 / 2310 ^ 2 * (1 / ((s : ℝ) - 1) - 1 / ((s : ℝ) + B - 1)) := by
        gcongr
        exact A19_tele s hs B
    _ ≤ 480 / 2310 ^ 2 * (1 / ((s : ℝ) - 1)) := by nlinarith

/-! ### The odd primorial -/

theorem A19_R_le (y : ℕ) : A19_oddPrimorial y ≤ 4 ^ y := by
  calc A19_oddPrimorial y ≤ primorial y := by
        apply Nat.le_of_dvd (primorial_pos y)
        unfold A19_oddPrimorial primorial
        apply Finset.prod_dvd_prod_of_subset
        intro p hp
        simp only [mem_filter] at hp ⊢
        exact ⟨hp.1, hp.2.1⟩
    _ ≤ 4 ^ y := primorial_le_four_pow y

theorem A19_R_pos (y : ℕ) : 0 < A19_oddPrimorial y := by
  unfold A19_oddPrimorial
  apply Finset.prod_pos
  intro p hp
  simp only [mem_filter] at hp
  exact hp.2.1.pos

theorem A19_dvd_R (y p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (hy : p ≤ y) : p ∣ A19_oddPrimorial y := by
  unfold A19_oddPrimorial
  apply Finset.dvd_prod_of_mem
  simp only [mem_filter, mem_range]
  exact ⟨by omega, hp, h2⟩

theorem A19_coprime_R (y p : ℕ) (hp : p.Prime) (hy : y < p) : Nat.Coprime p (A19_oddPrimorial y) := by
  unfold A19_oddPrimorial
  apply Nat.Coprime.prod_right
  intro q hq
  simp only [mem_filter, mem_range] at hq
  exact (Nat.coprime_primes hp hq.2.1).2 (by omega)

theorem A19_R_odd (y : ℕ) : A19_oddPrimorial y % 2 = 1 := by
  have h : Nat.Coprime 2 (A19_oddPrimorial y) := by
    unfold A19_oddPrimorial
    apply Nat.Coprime.prod_right
    intro q hq
    simp only [mem_filter, mem_range] at hq
    exact (Nat.coprime_primes Nat.prime_two hq.2.1).2 (Ne.symm hq.2.2)
  rcases Nat.mod_two_eq_zero_or_one (A19_oddPrimorial y) with h0 | h1
  · exfalso
    have : 2 ∣ A19_oddPrimorial y := Nat.dvd_of_mod_eq_zero h0
    have := Nat.Coprime.eq_one_of_dvd h this
    omega
  · exact h1

theorem A19_four_pow (y : ℕ) : 4 * 4 ^ y = 2 ^ (2 * y + 2) := by
  rw [show 2 * y + 2 = 2 * (y + 1) by ring, pow_mul, pow_succ]
  norm_num
  ring

/-! ### Final arithmetic: 25 (2 L 2^L + 2) < 2 · 2^L · 2^17 · 2^s · E -/

theorem A19_final (s L P T E : ℕ) (hs : 20 ≤ s) (hL : L = 4851 * s) (hT : s < T)
    (hE : 1 ≤ E) (hP : 1 ≤ P) :
    25 * (2 * L * P + 2) < 2 * (P * (2 ^ 17 * (T * E))) := by
  have h1 : 1 ≤ s * P := Nat.mul_pos (by omega) hP
  have h2 : s * P < T * P := Nat.mul_lt_mul_of_pos_right hT hP
  have h3 : T * P ≤ T * E * P := by
    rw [Nat.mul_right_comm]
    exact Nat.le_mul_of_pos_right _ hE
  have e1 : 2 * L * P = 9702 * (s * P) := by rw [hL]; ring
  have e2 : 2 * (P * (2 ^ 17 * (T * E))) = 262144 * (T * E * P) := by ring
  rw [e1, e2]
  omega

/-! ### Main counting step -/

theorem A19_exists (s : ℕ) (hs : 20 ≤ s) :
    ∃ n, s < n ∧ ∀ k : ℕ, 2 ^ k < n → Squarefree (n - 2 ^ k) := by
  set y := 2310 * s with hy
  set L := 4851 * s with hLdef
  set K := 2 * L with hKdef
  set x := 2 ^ K with hx
  set R := A19_oddPrimorial y with hRdef
  set M := 4 * R with hM
  have hRpos : 0 < R := A19_R_pos y
  have hMpos : 0 < M := by omega
  have hRodd : R % 2 = 1 := A19_R_odd y
  set c := if R % 4 = 1 then 3 * R else R with hcdef
  have hc4 : c % 4 = 3 := by
    rw [hcdef]; split_ifs with h <;> omega
  have hcR : R ∣ c := by
    rw [hcdef]; split_ifs
    · exact Dvd.intro_left 3 rfl
    · exact dvd_refl R
  have hcM : c < M := by rw [hcdef]; split_ifs <;> omega
  have hRc : R ≤ c := by rw [hcdef]; split_ifs <;> omega
  -- M ≤ 2^(2y+2) and x = 2^(2y+2) * D
  --
  have hMle : M ≤ 2 ^ (2 * y + 2) := by
    have := A19_R_le y
    calc M = 4 * R := rfl
      _ ≤ 4 * 4 ^ y := by omega
      _ = 2 ^ (2 * y + 2) := A19_four_pow y
  set D := 2 ^ (K - (2 * y + 2)) with hD
  have hxD : x = 2 ^ (2 * y + 2) * D := by
    rw [hx, hD, ← pow_add]; congr 1; omega
  set J := x / M - 1 with hJ
  set cand := (range J).image (fun j => c + M * j) with hcand
  have hcand_card : cand.card = J := by
    rw [hcand, Finset.card_image_of_injective]
    · simp
    · intro a b hab
      simp only at hab
      have : M * a = M * b := by omega
      exact Nat.eq_of_mul_eq_mul_left hMpos this
  have hcand_mem : ∀ n ∈ cand, ∃ j, n = c + M * j ∧ j < J := by
    intro n hn
    rw [hcand, mem_image] at hn
    obtain ⟨j, hj, rfl⟩ := hn
    exact ⟨j, rfl, mem_range.1 hj⟩
  have hcand_le : ∀ n ∈ cand, n ≤ x := by
    intro n hn
    obtain ⟨j, rfl, hj⟩ := hcand_mem n hn
    have h1 : j + 1 ≤ x / M := by omega
    have h2 : M * (j + 1) ≤ M * (x / M) := Nat.mul_le_mul_left M h1
    have h3 : M * (x / M) ≤ x := Nat.mul_div_le x M
    have h4 : M * (j + 1) = M * j + M := by ring
    omega
  have hcand_mod4 : ∀ n ∈ cand, n % 4 = 3 := by
    intro n hn
    obtain ⟨j, rfl, _⟩ := hcand_mem n hn
    rw [show M * j = 4 * (R * j) by rw [hM]; ring]
    omega
  have hcand_R : ∀ n ∈ cand, R ∣ n := by
    intro n hn
    obtain ⟨j, rfl, _⟩ := hcand_mem n hn
    exact dvd_add hcR (Dvd.dvd.mul_right (Dvd.intro_left 4 rfl) j)
  have hcand_modM : ∀ n ∈ cand, n ≡ c [MOD M] := by
    intro n hn
    obtain ⟨j, rfl, _⟩ := hcand_mem n hn
    exact Nat.add_mul_mod_self_left c M j
  -- Large primes and bad sets
  --
  set Ps := (Ioc y (2 ^ L)).filter Nat.Prime with hPs
  set bad := fun (k p : ℕ) => cand.filter (fun n => 2 ^ k < n ∧ p ^ 2 ∣ n - 2 ^ k) with hbad
  have hbad_card : ∀ k, ∀ p ∈ Ps, (bad k p).card ≤ x / (M * p ^ 2) + 1 := by
    intro k p hp
    simp only [hPs, mem_filter, mem_Ioc] at hp
    have hp4 : Nat.Coprime p 4 := by
      apply (Nat.Prime.coprime_iff_not_dvd hp.2).2
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega
    have hcop : Nat.Coprime M (p ^ 2) :=
      ((Nat.Coprime.mul_right hp4 (A19_coprime_R y p hp.2 hp.1.1)).pow_left 2).symm
    apply A19_card_le_of_modEq _ x _
    · intro n hn
      exact hcand_le n (mem_filter.1 hn).1
    · intro a ha b hb
      simp only [hbad, mem_filter] at ha hb
      apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).1
      constructor
      · exact (hcand_modM a ha.1).trans (hcand_modM b hb.1).symm
      · have h1 : 2 ^ k ≡ a [MOD p ^ 2] := (Nat.modEq_iff_dvd' ha.2.1.le).2 ha.2.2
        have h2 : 2 ^ k ≡ b [MOD p ^ 2] := (Nat.modEq_iff_dvd' hb.2.1.le).2 hb.2.2
        exact h1.symm.trans h2
  -- Every bad candidate lies in some bad set
  --
  have hcover : ∀ n ∈ cand, ¬ (∀ k : ℕ, 2 ^ k < n → Squarefree (n - 2 ^ k)) →
      n ∈ (range K).biUnion (fun k => Ps.biUnion (fun p => bad k p)) := by
    intro n hn hng
    push Not at hng
    obtain ⟨k, hk, hsq⟩ := hng
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    push Not at hsq
    obtain ⟨p, hp, hpp⟩ := hsq
    have hn4 := hcand_mod4 n hn
    have hnx := hcand_le n hn
    have hkK : k < K := by
      have : 2 ^ k < 2 ^ K := lt_of_lt_of_le hk hnx
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
    have hp2 : p ≠ 2 := by
      rintro rfl
      have h4 : 4 ∣ n - 2 ^ k := by simpa using hpp
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · interval_cases k <;> simp only [pow_zero, pow_one] at h4 <;> omega
      · have : 2 ^ k = 4 * 2 ^ (k - 2) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
        omega
    have hpy : y < p := by
      by_contra hle
      push Not at hle
      have h1 : p ∣ n := (A19_dvd_R y p hp hp2 hle).trans (hcand_R n hn)
      have h2 : p ∣ n - 2 ^ k := (Dvd.intro p rfl).trans hpp
      have h3 : p ∣ n - (n - 2 ^ k) := Nat.dvd_sub h1 h2
      rw [Nat.sub_sub_self hk.le] at h3
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
      exact hp2 this
    have hpL : p ≤ 2 ^ L := by
      have h1 : p * p ≤ n - 2 ^ k := Nat.le_of_dvd (by omega) hpp
      have h2 : n - 2 ^ k < 2 ^ L * 2 ^ L := by
        rw [← pow_add, show L + L = K by omega]
        exact lt_of_lt_of_le (Nat.sub_lt (by omega) (Nat.two_pow_pos k)) hnx
      by_contra hc
      push Not at hc
      have : 2 ^ L * 2 ^ L < p * p := Nat.mul_lt_mul'' hc hc
      omega
    simp only [mem_biUnion, mem_range]
    refine ⟨k, hkK, p, ?_, ?_⟩
    · simp only [hPs, mem_filter, mem_Ioc]; exact ⟨⟨hpy, hpL⟩, hp⟩
    · simp only [hbad, mem_filter]; exact ⟨hn, hk, by rw [sq]; exact hpp⟩
  -- Real-number bounds
  --
  set a : ℝ := (x : ℝ) / M with ha
  set σ : ℝ := 480 / 2310 ^ 2 * (1 / ((s : ℝ) - 1)) with hσ
  have hs20 : (20 : ℝ) ≤ s := by exact_mod_cast hs
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hS : ∑ p ∈ Ps, (1 : ℝ) / (p : ℝ) ^ 2 ≤ σ := by
    calc ∑ p ∈ Ps, (1 : ℝ) / (p : ℝ) ^ 2
        ≤ ∑ m ∈ (Ioc (2310 * s) (2 ^ L)).filter (fun m => Nat.Coprime 2310 m),
            (1 : ℝ) / (m : ℝ) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            simp only [hPs, mem_filter, mem_Ioc] at hp ⊢
            refine ⟨hp.1, ?_⟩
            apply Nat.Coprime.symm
            apply (Nat.Prime.coprime_iff_not_dvd hp.2).2
            intro h
            have := Nat.le_of_dvd (by norm_num) h
            omega
          · intros; positivity
      _ ≤ σ := A19_sum_coprime s (2 ^ L) (by omega)
  have hPcard : (Ps.card : ℝ) ≤ 2 ^ L := by
    have : Ps.card ≤ 2 ^ L := by
      calc Ps.card ≤ (Ioc y (2 ^ L)).card := Finset.card_filter_le _ _
        _ = 2 ^ L - y := Nat.card_Ioc _ _
        _ ≤ 2 ^ L := Nat.sub_le _ _
    exact_mod_cast this
  have hinner : ∀ k ∈ range K, (∑ p ∈ Ps, (((x / (M * p ^ 2) : ℕ) : ℝ) + 1)) ≤ a * σ + 2 ^ L := by
    intro k _
    have hterm : ∀ p ∈ Ps, (((x / (M * p ^ 2) : ℕ) : ℝ) + 1) ≤ a * (1 / (p : ℝ) ^ 2) + 1 := by
      intro p _
      have h1 : (((x / (M * p ^ 2) : ℕ) : ℝ)) ≤ (x : ℝ) / ((M * p ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
      have h2 : (x : ℝ) / ((M * p ^ 2 : ℕ) : ℝ) = a * (1 / (p : ℝ) ^ 2) := by
        rw [ha]; push_cast; ring
      linarith
    have ha0 : 0 ≤ a := by positivity
    calc ∑ p ∈ Ps, (((x / (M * p ^ 2) : ℕ) : ℝ) + 1)
        ≤ ∑ p ∈ Ps, (a * (1 / (p : ℝ) ^ 2) + 1) := Finset.sum_le_sum hterm
      _ = a * ∑ p ∈ Ps, (1 / (p : ℝ) ^ 2) + Ps.card := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]; simp
      _ ≤ a * σ + 2 ^ L := by
          have := mul_le_mul_of_nonneg_left hS ha0
          linarith
  -- If no candidate is good, J ≤ K (a σ + 2^L)
  --
  by_contra hnone
  push Not at hnone
  have hall : ∀ n ∈ cand, ¬ (∀ k : ℕ, 2 ^ k < n → Squarefree (n - 2 ^ k)) := by
    intro n hn hg
    have hRs : s < R := by
      obtain ⟨q, hq, hq1, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul (1155 * s) (by omega)
      have hqR : q ∣ R := A19_dvd_R y q hq (by omega) (by omega)
      have := Nat.le_of_dvd hRpos hqR
      omega
    have hRn : R ≤ n := by
      obtain ⟨j, rfl, _⟩ := hcand_mem n hn
      omega
    obtain ⟨k, hk, hk2⟩ := hnone n (by omega)
    exact hk2 (hg k hk)
  have hJle : J ≤ ∑ k ∈ range K, ∑ p ∈ Ps, (x / (M * p ^ 2) + 1) := by
    rw [← hcand_card]
    calc cand.card ≤ ((range K).biUnion (fun k => Ps.biUnion (fun p => bad k p))).card :=
          Finset.card_le_card (fun n hn => hcover n hn (hall n hn))
      _ ≤ ∑ k ∈ range K, (Ps.biUnion (fun p => bad k p)).card := Finset.card_biUnion_le
      _ ≤ ∑ k ∈ range K, ∑ p ∈ Ps, (bad k p).card :=
          Finset.sum_le_sum (fun k _ => Finset.card_biUnion_le)
      _ ≤ ∑ k ∈ range K, ∑ p ∈ Ps, (x / (M * p ^ 2) + 1) :=
          Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun p hp => hbad_card k p hp))
  have hJr : (J : ℝ) ≤ K * (a * σ + 2 ^ L) := by
    have h1 : (J : ℝ) ≤ ∑ k ∈ range K, ∑ p ∈ Ps, (((x / (M * p ^ 2) : ℕ) : ℝ) + 1) := by
      exact_mod_cast hJle
    have h2 : ∑ k ∈ range K, ∑ p ∈ Ps, (((x / (M * p ^ 2) : ℕ) : ℝ) + 1)
        ≤ ∑ k ∈ range K, (a * σ + 2 ^ L) := Finset.sum_le_sum hinner
    have h3 : ∑ k ∈ range K, (a * σ + 2 ^ L) = K * (a * σ + 2 ^ L) := by
      rw [Finset.sum_const, card_range, nsmul_eq_mul]
    linarith
  -- J ≥ a - 2
  --
  have hD1 : 1 ≤ D := Nat.one_le_two_pow
  have hxM : M ≤ x := by
    rw [hxD]; calc M ≤ 2 ^ (2 * y + 2) := hMle
      _ = 2 ^ (2 * y + 2) * 1 := by ring
      _ ≤ 2 ^ (2 * y + 2) * D := Nat.mul_le_mul_left _ hD1
  have hq1 : 1 ≤ x / M := (Nat.one_le_div_iff hMpos).2 hxM
  have hJa : a - 2 ≤ (J : ℝ) := by
    have h1 : x < M * (x / M + 1) := Nat.lt_mul_div_succ x hMpos
    have h2 : (x : ℝ) < M * (((x / M : ℕ) : ℝ) + 1) := by exact_mod_cast h1
    have h3 : a < ((x / M : ℕ) : ℝ) + 1 := by
      rw [ha, div_lt_iff₀ hMr]; linarith
    have h4 : (J : ℝ) = ((x / M : ℕ) : ℝ) - 1 := by
      rw [hJ, Nat.cast_sub hq1]; simp
    linarith
  -- a ≥ D
  --
  have haD : (D : ℝ) ≤ a := by
    rw [ha, le_div_iff₀ hMr]
    have h1 : (M : ℝ) ≤ 2 ^ (2 * y + 2) := by exact_mod_cast hMle
    have h2 : (x : ℝ) = 2 ^ (2 * y + 2) * D := by rw [hxD]; push_cast; ring
    have h3 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    nlinarith
  -- K σ ≤ 23/25
  --
  have hKσ : (K : ℝ) * σ ≤ 23 / 25 := by
    have hK : (K : ℝ) = 9702 * s := by rw [hKdef, hLdef]; push_cast; ring
    have hs1 : (0 : ℝ) < (s : ℝ) - 1 := by linarith
    rw [hK, hσ, show (9702 : ℝ) * s * (480 / 2310 ^ 2 * (1 / ((s : ℝ) - 1)))
        = (4656960 * s) / (5336100 * ((s : ℝ) - 1)) by field_simp; ring]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- Combine: 2a/25 ≤ K 2^L + 2, so 2 D ≤ 25 (K 2^L + 2)
  --
  have ha0 : 0 ≤ a := by positivity
  have hfin : (2 : ℝ) * D ≤ 25 * (K * 2 ^ L + 2) := by
    have : (K : ℝ) * (a * σ) ≤ 23 / 25 * a := by nlinarith
    nlinarith
  have hfinN : 2 * D ≤ 25 * (K * 2 ^ L + 2) := by exact_mod_cast hfin
  -- But D = 2^L · 2^18 · 2^s · 2^(230 s - 20), far larger
  --
  have hDsplit : D = 2 ^ L * (2 ^ 17 * (2 ^ s * 2 ^ (230 * s - 19))) := by
    rw [hD, ← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  have hs2 : s < 2 ^ s := Nat.lt_two_pow_self
  have hE : 1 ≤ 2 ^ (230 * s - 19) := Nat.one_le_two_pow
  have hP : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have hfinal := A19_final s L (2 ^ L) (2 ^ s) (2 ^ (230 * s - 19)) hs hLdef hs2 hE hP
  rw [hDsplit] at hfinN
  exact absurd hfinN (not_le.2 (by rw [hKdef]; exact hfinal))

/-! ### Infinitude -/

theorem A19_2_main :
    Set.Infinite {n : ℕ | ∀ k : ℕ, 2 ^ k < n → Squarefree (n - 2 ^ k)} := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨n, hn, hg⟩ := A19_exists (max a 20) (le_max_right _ _)
  exact ⟨n, hg, lt_of_le_of_lt (le_max_left _ _) hn⟩

