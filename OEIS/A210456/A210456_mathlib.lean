import Mathlib
import OpenProblemsLib.Dwork

/-!
# OEIS A210456: periods of n-step Fibonacci numbers mod 9 are divisible by 3

`nb n` is the `n`-step Fibonacci sequence started `0, …, 0, 1`; `a210456 n` is its least period
mod 9 (the README's reading of the digital-root period).

Proved here:
* `exists_period`, `a210456_spec`: the sequence is purely periodic mod 9 and `a210456 n` is its
  least positive period.
* `three_dvd_of_period`, `A210456_three_dvd`: for `n ≥ 2` every period mod 9 is divisible by 3,
  so `3 ∣ a(n)` (the entry's first conjecture).

Route: the power sums `ps n m` of the roots of `xⁿ - xⁿ⁻¹ - … - 1` are the coefficients of
`B = N / P` with `P = 1 - x - … - xⁿ`, `N = -θP`; `θ(1/P) = B/P`, so `exp(∑ ps(m) x^m/m) = 1/P` has
integer coefficients and Dwork's lemma (`OpenProblemsLib.Dwork.gauss_of_expCoeff_int`) gives
`9 ∣ ps(9t) - ps(3t)`. The power sums satisfy the same recurrence, so every period of `nb n`
mod 9 is a period of `ps` (`periodic_of_rec`). A period `Q` prime to 3 would give
`ps 3 ≡ ps 1 (mod 9)`, but `ps 3 - ps 1` is 3 (n = 2) or 6 (n ≥ 3).

Outside Lean: Helenius's closed forms `a(3^m - 1) = 3^(2m+1) - 3` and
`a(3^m) = 3^(2m+1) + 3^(m+1) + 3` (the mod-3 periods via generation of `F_{q²}^*` and Singer
difference sets in `PG(2, q)`, and `a = 3P`), argued in the README.
-/

open PowerSeries Finset OpenProblemsLib.Dwork

/-- The `n`-step Fibonacci numbers started `0, …, 0, 1` (`n - 1` zeros). -/
def nb (n : ℕ) (k : ℕ) : ℤ :=
  if _h : k + 1 < n then 0 else if _h' : k + 1 = n then 1 else ∑ i : Fin n, nb n (k - n + i)
termination_by k
decreasing_by have := i.isLt; omega

lemma nb_of_lt {n k : ℕ} (h : k + 1 < n) : nb n k = 0 := by
  rw [nb]; simp [h]

lemma nb_init {n : ℕ} (hn : 1 ≤ n) : nb n (n - 1) = 1 := by
  rw [nb]; simp [show n - 1 + 1 = n by omega]

lemma nb_rec (n k : ℕ) : nb n (k + n) = ∑ i : Fin n, nb n (k + i) := by
  rw [nb]
  simp only [show ¬(k + n + 1 < n) from by omega, show ¬(k + n + 1 = n) from by omega,
    ↓reduceDIte]
  refine sum_congr rfl fun i _ => ?_
  congr 1; omega

section Series

variable (n : ℕ)

/-- `P = 1 - x - x² - … - xⁿ`. -/
noncomputable def Pn : ℤ⟦X⟧ := 1 - ∑ i ∈ range n, X ^ (i + 1)

lemma constantCoeff_Pn : constantCoeff (Pn n) = 1 := by
  simp [Pn, map_sum]

/-- `A = 1 / P`. -/
noncomputable def An : ℤ⟦X⟧ := PowerSeries.invOfUnit (Pn n) 1

lemma An_mul_Pn : An n * Pn n = 1 :=
  invOfUnit_mul _ _ (by rw [constantCoeff_Pn]; rfl)

lemma constantCoeff_An : constantCoeff (An n) = 1 := by
  rw [An, constantCoeff_invOfUnit]; simp

lemma coeff_mul_Pn (F : ℤ⟦X⟧) (m : ℕ) :
    coeff m (F * Pn n) =
      coeff m F - ∑ i ∈ range n, if i + 1 ≤ m then coeff (m - (i + 1)) F else 0 := by
  rw [Pn, mul_sub, mul_one, mul_sum, map_sub, map_sum]
  congr 1
  exact sum_congr rfl fun i _ => coeff_mul_X_pow' F (i + 1) m

/-- `nb n k` is the coefficient of `x^k` in `x^{n-1} / P`. -/
lemma nb_eq_coeff (hn : 1 ≤ n) (k : ℕ) : nb n k = coeff k (X ^ (n - 1) * An n) := by
  set G := X ^ (n - 1) * An n with hG
  have hGP : G * Pn n = X ^ (n - 1) := by rw [hG, mul_assoc, An_mul_Pn, mul_one]
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases lt_or_ge (k + 1) n with h | h
    · rw [nb_of_lt h, hG, coeff_X_pow_mul', ite_eq_right (by omega)]
    · rcases Nat.eq_or_lt_of_le h with h | h
      · rw [show k = n - 1 by omega, nb_init hn, hG, coeff_X_pow_mul', ite_eq_left le_rfl,
          Nat.sub_self, coeff_zero_eq_constantCoeff_apply, constantCoeff_An]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + n := ⟨k - n, by omega⟩
        rw [nb_rec n j]
        have e := congrArg (coeff (j + n)) hGP
        rw [coeff_mul_Pn, coeff_X_pow, ite_eq_right (by omega)] at e
        have e2 : coeff (j + n) G = ∑ i ∈ range n, coeff (j + i) G := by
          rw [sub_eq_zero.1 e]
          rw [sum_congr rfl fun i hi => ite_eq_left (by have := mem_range.1 hi; omega)]
          rw [← sum_range_reflect (fun i => coeff (j + i) G) n]
          refine sum_congr rfl fun i hi => ?_
          have := mem_range.1 hi
          rw [show j + n - (i + 1) = j + (n - 1 - i) by omega]
        rw [e2, ← Fin.sum_univ_eq_sum_range (fun i => coeff (j + i) G) n]
        exact sum_congr rfl fun i _ => ih (j + i) (by have := i.isLt; omega)

/-- `N = x + 2x² + … + n xⁿ = -θ P`. -/
noncomputable def Nn : ℤ⟦X⟧ := ∑ i ∈ range n, C ((i + 1 : ℕ) : ℤ) * X ^ (i + 1)

lemma theta_Pn : theta (Pn n) = -Nn n := by
  ext m
  rw [coeff_theta, map_neg, Pn, Nn, map_sub, map_sum, map_sum, coeff_one, mul_sub, mul_sum]
  have h1 : (m : ℤ) * (if m = 0 then 1 else 0) = 0 := by split_ifs with h <;> simp [h]
  rw [h1, zero_sub]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [coeff_X_pow, coeff_C_mul_X_pow]
  split_ifs with h
  · subst h; simp
  · simp

/-- `B = N / P`, the logarithmic derivative `θA / A`; its coefficients are the power sums of the
roots of `xⁿ - xⁿ⁻¹ - … - 1`. -/
noncomputable def Bn : ℤ⟦X⟧ := Nn n * An n

lemma LD_An : LD (An n) (Bn n) := by
  unfold LD
  have h0 : theta (An n * Pn n) = 0 := by rw [An_mul_Pn, theta_one]
  rw [theta_mul, theta_Pn] at h0
  have h1 : theta (An n) * Pn n = An n * Nn n := by linear_combination h0
  calc theta (An n) = theta (An n) * (Pn n * An n) := by rw [mul_comm (Pn n), An_mul_Pn, mul_one]
    _ = (theta (An n) * Pn n) * An n := by ring
    _ = Bn n * An n := by rw [h1, Bn]; ring

/-- The power sums `s_m = [x^m] B`. -/
noncomputable def ps (m : ℕ) : ℤ := coeff m (Bn n)

lemma ps_gauss (p : ℕ) (hp : p.Prime) : LGp p (ps n) := by
  refine gauss_of_expCoeff_int (ps n) (fun k => ⟨coeff k (An n), ?_⟩) p hp
  exact expCoeff_eq (ps n) (An n) (Bn n) (LD_An n) (constantCoeff_An n) k
    (fun j _ _ => rfl) k le_rfl

lemma Bn_mul_Pn : Bn n * Pn n = Nn n := by
  rw [Bn, mul_assoc, An_mul_Pn, mul_one]

lemma ps_rec (k : ℕ) : ps n (k + 1 + n) = ∑ i : Fin n, ps n (k + 1 + i) := by
  have e := congrArg (coeff (k + 1 + n)) (Bn_mul_Pn n)
  rw [coeff_mul_Pn] at e
  have hN : coeff (k + 1 + n) (Nn n) = 0 := by
    rw [Nn, map_sum]
    refine sum_eq_zero fun i hi => ?_
    rw [coeff_C_mul_X_pow, ite_eq_right (by have := mem_range.1 hi; omega)]
  rw [hN, sub_eq_zero] at e
  unfold ps
  rw [e, sum_congr rfl fun i hi => ite_eq_left (by have := mem_range.1 hi; omega),
    Fin.sum_univ_eq_sum_range (fun i => coeff (k + 1 + i) (Bn n)) n,
    ← sum_range_reflect (fun i => coeff (k + 1 + i) (Bn n)) n]
  refine sum_congr rfl fun i hi => ?_
  have := mem_range.1 hi
  rw [show k + 1 + n - (i + 1) = k + 1 + (n - 1 - i) by omega]

lemma coeff_An_one (hn : 1 ≤ n) : coeff 1 (An n) = 1 := by
  have e := congrArg (coeff 1) (An_mul_Pn n)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [coeff_mul_Pn, coeff_one, sum_range_succ', sum_eq_zero fun i hi => ite_eq_right (by omega),
    zero_add, ite_eq_left (by omega), Nat.sub_self, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_An] at e
  simpa [sub_eq_zero] using e

lemma coeff_An_two (hn : 2 ≤ n) : coeff 2 (An n) = 2 := by
  have e := congrArg (coeff 2) (An_mul_Pn n)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [coeff_mul_Pn, coeff_one, sum_range_succ', sum_range_succ',
    sum_eq_zero fun i hi => ite_eq_right (by omega), zero_add, ite_eq_left (by omega),
    ite_eq_left (by omega), show 2 - (1 + 1) = 0 by rfl, show 2 - (0 + 1) = 1 by rfl,
    coeff_An_one _ (by omega), coeff_zero_eq_constantCoeff_apply, constantCoeff_An] at e
  simp only [OfNat.ofNat_ne_zero, ite_false] at e
  linarith

lemma ps_apply (m : ℕ) :
    ps n m = ∑ i ∈ range n, ((i + 1 : ℕ) : ℤ) *
      (if i + 1 ≤ m then coeff (m - (i + 1)) (An n) else 0) := by
  rw [ps, Bn, Nn, sum_mul, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']

lemma ps_one (hn : 1 ≤ n) : ps n 1 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [ps_apply, sum_range_succ', sum_eq_zero fun i hi => by rw [ite_eq_right (by omega), mul_zero],
    zero_add, ite_eq_left (by omega), Nat.sub_self, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_An]
  norm_num

lemma ps_three_sub_one (hn : 2 ≤ n) : ps n 3 - ps n 1 = 3 ∨ ps n 3 - ps n 1 = 6 := by
  rw [ps_one n (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [ps_apply, sum_range_succ', sum_range_succ', ite_eq_left (by omega), ite_eq_left (by omega),
    show 3 - (1 + 1) = 1 by rfl, show 3 - (0 + 1) = 2 by rfl, coeff_An_one _ (by omega),
    coeff_An_two _ (by omega)]
  rcases m with _ | m
  · left; simp
  · right
    rw [sum_range_succ', sum_eq_zero fun i hi => by rw [ite_eq_right (by omega), mul_zero],
      zero_add, ite_eq_left (by omega), show 3 - (0 + 2 + 1) = 0 by rfl,
      coeff_zero_eq_constantCoeff_apply, constantCoeff_An]
    norm_num

end Series

/-- Every recurrence sequence is periodic mod 9 with any period of `nb n` (shifts of `nb n`
span all solutions). Induction on the number `j` of free initial values. -/
lemma periodic_of_rec (n Q : ℕ) (hn : 1 ≤ n) (hu : ∀ k, (9 : ℤ) ∣ nb n (k + Q) - nb n k) :
    ∀ j, j ≤ n → ∀ w : ℕ → ℤ, (∀ k, w (k + n) = ∑ i : Fin n, w (k + i)) →
      (∀ i, i < n - j → w i = 0) → ∀ k, (9 : ℤ) ∣ w (k + Q) - w k := by
  intro j
  induction j with
  | zero =>
    intro _ w hw hz
    have h0 : ∀ k, w k = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        rcases lt_or_ge k n with h | h
        · exact hz k (by omega)
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + n := ⟨k - n, by omega⟩
          rw [hw]
          exact sum_eq_zero fun i _ => ih _ (by have := i.isLt; omega)
    intro k; rw [h0, h0]; simp
  | succ j ih =>
    intro hj w hw hz
    set r := n - (j + 1) with hr
    set c := w r with hc
    set w' : ℕ → ℤ := fun k => w k - c * nb n (k + (n - 1 - r)) with hw'
    have hw'rec : ∀ k, w' (k + n) = ∑ i : Fin n, w' (k + i) := by
      intro k
      simp only [hw']
      rw [hw, sum_sub_distrib, ← mul_sum, show k + n + (n - 1 - r) = (k + (n - 1 - r)) + n by omega,
        nb_rec]
      congr 2
      exact sum_congr rfl fun i _ => by congr 1; omega
    have hw'z : ∀ i, i < n - j → w' i = 0 := by
      intro i hi
      simp only [hw']
      rcases Nat.lt_or_ge i r with h | h
      · rw [hz i (by omega), nb_of_lt (by omega)]; ring
      · rw [show i = r by omega, show r + (n - 1 - r) = n - 1 by omega, nb_init hn, hc]; ring
    have h1 := ih (by omega) w' hw'rec hw'z
    intro k
    have h2 := hu (k + (n - 1 - r))
    have h3 := h1 k
    simp only [hw'] at h3
    rw [show k + Q + (n - 1 - r) = k + (n - 1 - r) + Q by omega] at h3
    have : w (k + Q) - w k = (w (k + Q) - c * nb n (k + (n - 1 - r) + Q) -
        (w k - c * nb n (k + (n - 1 - r)))) + c * (nb n (k + (n - 1 - r) + Q) -
          nb n (k + (n - 1 - r))) := by ring
    rw [this]
    exact dvd_add h3 (dvd_mul_of_dvd_right h2 c)

/-- **Main theorem.** For `n ≥ 2`, every period of the `n`-step Fibonacci numbers mod 9 is
divisible by 3. -/
theorem three_dvd_of_period (n : ℕ) (hn : 2 ≤ n) (Q : ℕ) (hQ : 0 < Q)
    (hu : ∀ k, (9 : ℤ) ∣ nb n (k + Q) - nb n k) : 3 ∣ Q := by
  by_contra h3
  set R := 2 * Q with hR
  have huR : ∀ k, (9 : ℤ) ∣ nb n (k + R) - nb n k := by
    intro k
    have : nb n (k + R) - nb n k = (nb n ((k + Q) + Q) - nb n (k + Q)) + (nb n (k + Q) - nb n k) := by
      rw [show k + Q + Q = k + R by omega]; ring
    rw [this]; exact dvd_add (hu _) (hu _)
  set w : ℕ → ℤ := fun k => ps n (k + 1) with hwdef
  have hw : ∀ k, w (k + n) = ∑ i : Fin n, w (k + i) := by
    intro k
    simp only [hwdef]
    rw [show k + n + 1 = k + 1 + n by omega, ps_rec]
    exact sum_congr rfl fun i _ => by congr 1; omega
  have hper := periodic_of_rec n R (by omega) huR n le_rfl w hw (fun i hi => by omega)
  have hiter : ∀ c k, (9 : ℤ) ∣ w (k + c * R) - w k := by
    intro c
    induction c with
    | zero => intro k; simp
    | succ c ih =>
      intro k
      have : w (k + (c + 1) * R) - w k = (w ((k + c * R) + R) - w (k + c * R)) +
          (w (k + c * R) - w k) := by
        rw [show k + c * R + R = k + (c + 1) * R by ring]; ring
      rw [this]; exact dvd_add (hper _) (ih k)
  have cop : Nat.Coprime 3 R := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · norm_num at h
    · exact h3 h
  have hR2 : 2 ≤ R := by omega
  have hEuler := Nat.ModEq.pow_totient cop
  have htot : 1 ≤ Nat.totient R := Nat.totient_pos.2 (by omega)
  set T := 3 ^ Nat.totient R with hT
  set c := T / R with hcdef
  have hTc : T = R * c + 1 := by
    have h1 : T % R = 1 := by
      have := hEuler
      unfold Nat.ModEq at this
      rw [this, Nat.mod_eq_of_lt (by omega)]
    calc T = R * (T / R) + T % R := (Nat.div_add_mod T R).symm
      _ = R * c + 1 := by rw [h1]
  set t := 3 ^ (Nat.totient R - 1) with htdef
  have ht3 : t * 3 = T := by
    rw [htdef, hT, ← pow_succ, Nat.sub_add_cancel htot]
  have hg := ps_gauss n 3 Nat.prime_three 2 t (by norm_num)
  have e1 : t * 3 ^ (2 - 1) = 0 + c * R + 1 := by rw [show 2 - 1 = 1 by rfl, pow_one, ht3, hTc]; ring
  have e2 : t * 3 ^ 2 = 2 + (3 * c) * R + 1 := by
    rw [show t * 3 ^ 2 = 3 * (t * 3) by ring, ht3, hTc]; ring
  rw [e1, e2] at hg
  have h1 := hiter c 0
  have h2 := hiter (3 * c) 2
  simp only [hwdef] at h1 h2
  have h4 : (9 : ℤ) ∣ ps n 3 - ps n 1 := by
    have : ps n 3 - ps n 1 = (ps n (2 + 3 * c * R + 1) - ps n (0 + c * R + 1)) -
        (ps n (2 + 3 * c * R + 1) - ps n (2 + 1)) + (ps n (0 + c * R + 1) - ps n (0 + 1)) := by
      ring
    rw [this]
    exact dvd_add (dvd_sub hg h2) h1
  rcases ps_three_sub_one n hn with h | h <;> rw [h] at h4 <;> norm_num at h4

/-- `a(n)`: the least period of the `n`-step Fibonacci numbers mod 9 (`0` if there were none). -/
noncomputable def a210456 (n : ℕ) : ℕ :=
  sInf {p | 0 < p ∧ ∀ k, (9 : ℤ) ∣ nb n (k + p) - nb n k}

/-- OEIS A210456, first conjecture: `3 ∣ a(n)` for `n ≥ 2`. -/
theorem A210456_three_dvd (n : ℕ) (hn : 2 ≤ n) : 3 ∣ a210456 n := by
  by_cases hne : {p | 0 < p ∧ ∀ k, (9 : ℤ) ∣ nb n (k + p) - nb n k}.Nonempty
  · have hmem := Nat.sInf_mem hne
    exact three_dvd_of_period n hn _ hmem.1 hmem.2
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [a210456, hne, Nat.sInf_empty]
    exact dvd_zero 3

/-- The sequence is purely periodic mod 9 (pigeonhole on windows of length `n`, the recurrence
runs both ways). -/
theorem exists_period (n : ℕ) (hn : 1 ≤ n) :
    ∃ p, 0 < p ∧ ∀ k, (9 : ℤ) ∣ nb n (k + p) - nb n k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let st : ℕ → (Fin (m + 1) → ZMod 9) := fun k i => ((nb (m + 1) (k + i) : ℤ) : ZMod 9)
  have fwd : ∀ a b, st a = st b → st (a + 1) = st (b + 1) := by
    intro a b h
    funext i
    simp only [st]
    by_cases hi : (i : ℕ) + 1 < m + 1
    · have := congrFun h ⟨i + 1, hi⟩
      simp only [st] at this
      rw [show a + 1 + (i : ℕ) = a + (i + 1) by omega, show b + 1 + (i : ℕ) = b + (i + 1) by omega]
      exact this
    · rw [show a + 1 + (i : ℕ) = a + (m + 1) by omega, show b + 1 + (i : ℕ) = b + (m + 1) by omega,
        nb_rec, nb_rec]
      push_cast
      exact sum_congr rfl fun j _ => congrFun h j
  have bwd : ∀ a b, st (a + 1) = st (b + 1) → st a = st b := by
    intro a b h
    funext i
    simp only [st]
    by_cases hi : (i : ℕ) = 0
    · have ra := nb_rec (m + 1) a
      have rb := nb_rec (m + 1) b
      rw [Fin.sum_univ_succ] at ra rb
      have ea : ((nb (m + 1) (a + i) : ℤ) : ZMod 9) = (nb (m + 1) (a + (m + 1)) : ZMod 9) -
          ∑ j : Fin m, (nb (m + 1) (a + ((j.succ : Fin (m + 1)) : ℕ)) : ZMod 9) := by
        rw [ra, hi]; simp only [Fin.val_zero, add_zero]; push_cast; ring
      have eb : ((nb (m + 1) (b + i) : ℤ) : ZMod 9) = (nb (m + 1) (b + (m + 1)) : ZMod 9) -
          ∑ j : Fin m, (nb (m + 1) (b + ((j.succ : Fin (m + 1)) : ℕ)) : ZMod 9) := by
        rw [rb, hi]; simp only [Fin.val_zero, add_zero]; push_cast; ring
      rw [ea, eb]
      have hlast := congrFun h ⟨m, by omega⟩
      simp only [st] at hlast
      rw [show a + 1 + m = a + (m + 1) by omega, show b + 1 + m = b + (m + 1) by omega] at hlast
      rw [hlast]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      have := congrFun h ⟨j, by omega⟩
      simp only [st] at this
      rw [Fin.val_succ, show a + ((j : ℕ) + 1) = a + 1 + j by omega,
        show b + ((j : ℕ) + 1) = b + 1 + j by omega]
      exact this
    · have := congrFun h ⟨i - 1, by omega⟩
      simp only [st] at this
      rw [show a + 1 + ((i : ℕ) - 1) = a + i by omega,
        show b + 1 + ((i : ℕ) - 1) = b + i by omega] at this
      exact this
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite st
  have key : ∀ i j, i < j → st i = st j → ∃ p, 0 < p ∧ ∀ k, st k = st (k + p) := by
    intro i j hlt heq
    refine ⟨j - i, by omega, ?_⟩
    have h0 : ∀ d, d ≤ i → st (i - d) = st (j - d) := by
      intro d
      induction d with
      | zero => intro _; simpa using heq
      | succ d ih =>
        intro hd
        apply bwd
        rw [show i - (d + 1) + 1 = i - d by omega, show j - (d + 1) + 1 = j - d by omega]
        exact ih (by omega)
    have hs0 := h0 i le_rfl
    rw [Nat.sub_self] at hs0
    intro k
    induction k with
    | zero => simpa using hs0
    | succ k ih =>
      rw [show k + 1 + (j - i) = k + (j - i) + 1 by omega]
      exact fwd _ _ ih
  obtain ⟨p, hp, hper⟩ : ∃ p, 0 < p ∧ ∀ k, st k = st (k + p) := by
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact key i j h heq
    · exact key j i h heq.symm
  refine ⟨p, hp, fun k => ?_⟩
  have := congrFun (hper k) 0
  simp only [st, Fin.val_zero, add_zero] at this
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 9).1 this

/-- `a(n)` is a genuine least period: positive, a period, and below every period. -/
theorem a210456_spec (n : ℕ) (hn : 1 ≤ n) :
    0 < a210456 n ∧ (∀ k, (9 : ℤ) ∣ nb n (k + a210456 n) - nb n k) ∧
      ∀ p, 0 < p → (∀ k, (9 : ℤ) ∣ nb n (k + p) - nb n k) → a210456 n ≤ p := by
  obtain ⟨p, hp, hper⟩ := exists_period n hn
  have hne : {p | 0 < p ∧ ∀ k, (9 : ℤ) ∣ nb n (k + p) - nb n k}.Nonempty := ⟨p, hp, hper⟩
  have hmem := Nat.sInf_mem hne
  exact ⟨hmem.1, hmem.2, fun q hq hqper => Nat.sInf_le ⟨hq, hqper⟩⟩
