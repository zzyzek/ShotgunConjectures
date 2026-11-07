import Mathlib
import OpenProblemsLib.Pratt

/-
Guy, UPINT B1 (Martin): with f multiplicative, f(p^e) = p^e - p^(e-1) + ... + (-1)^e, are there
n with n = k f(n) for k ≥ 4? (Such n are the k-imperfect numbers, OEIS A127724.) Known: k = 4
(OEIS A328860) and k = 5 (A. Wechsler, Seqfan/math-fun, 11 Feb 2020, a 208-digit number).

Checked here (`five_imperfect`): for Wechsler's 208-digit N, (N : ℤ) = 5 * rho N, where
rho = id ⋆ λ (Dirichlet convolution with the Liouville function, Mathlib). `rho_prime_pow`
shows rho(p^e) = Σ_{i ≤ e} p^i (-1)^(e-i), Martin's f on prime powers, and rho is
multiplicative (`rho_mult`), so rho is Martin's f. The factorization of N, primality of its
44 prime factors (Pratt certificates for the four above 10^5) and the 44 prime-power values are
checked. Not checked: anything about k ≥ 6, infinitude, or odd 3-imperfect numbers (open).
-/

namespace NT_B1_2

open ArithmeticFunction OpenProblemsLib

/-- rho = id ⋆ λ: rho n = Σ_{d ∣ n} d · λ(n / d). -/
def rho : ArithmeticFunction ℤ := (↑(ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) * liouville

theorem rho_mult : IsMultiplicative rho :=
  isMultiplicative_id.natCast.mul isMultiplicative_liouville

theorem rho_prime_pow (p e : ℕ) (hp : p.Prime) :
    rho (p ^ e) = ∑ i ∈ Finset.range (e + 1), (p : ℤ) ^ i * (-1) ^ (e - i) := by
  unfold rho
  rw [mul_apply]
  simp only [natCoe_apply, ArithmeticFunction.id_apply]
  rw [Nat.sum_divisorsAntidiagonal (fun x y => (x : ℤ) * liouville y),
    Nat.divisors_prime_pow hp, Finset.sum_map]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  simp only [Function.Embedding.coeFn_mk, Nat.cast_pow]
  rw [Nat.pow_div (by omega) hp.pos, liouville_apply (pow_ne_zero _ hp.ne_zero),
    cardFactors_apply_prime_pow hp]

theorem rmul {a b : ℕ} (h : Nat.Coprime a b) : rho (a * b) = rho a * rho b :=
  rho_mult.map_mul_of_coprime h

theorem bigprimes : ∀ p ∈ [139921, 178481, 2796203, 228511817], Nat.Prime p := by
  intro p hp
  have h := primes_of_prattCertifiesAll [139921, 178481, 2796203, 228511817] [⟨2, 1, []⟩,
      ⟨3, 2, [(2, 1)]⟩,
      ⟨5, 2, [(2, 2)]⟩,
      ⟨11, 2, [(2, 1), (5, 1)]⟩,
      ⟨13, 2, [(2, 2), (3, 1)]⟩,
      ⟨53, 2, [(2, 2), (13, 1)]⟩,
      ⟨139921, 7, [(2, 4), (3, 1), (5, 1), (11, 1), (53, 1)]⟩,
      ⟨23, 5, [(2, 1), (11, 1)]⟩,
      ⟨97, 5, [(2, 5), (3, 1)]⟩,
      ⟨178481, 3, [(2, 4), (5, 1), (23, 1), (97, 1)]⟩,
      ⟨89, 3, [(2, 3), (11, 1)]⟩,
      ⟨31, 3, [(2, 1), (3, 1), (5, 1)]⟩,
      ⟨683, 5, [(2, 1), (11, 1), (31, 1)]⟩,
      ⟨2796203, 5, [(2, 1), (23, 1), (89, 1), (683, 1)]⟩,
      ⟨61, 2, [(2, 2), (3, 1), (5, 1)]⟩,
      ⟨367, 6, [(2, 1), (3, 1), (61, 1)]⟩,
      ⟨41, 6, [(2, 3), (5, 1)]⟩,
      ⟨73, 5, [(2, 3), (3, 2)]⟩,
      ⟨5987, 2, [(2, 1), (41, 1), (73, 1)]⟩,
      ⟨228511817, 5, [(2, 3), (13, 1), (367, 1), (5987, 1)]⟩] (by decide +kernel)
  exact h p hp

theorem v2 : rho (2^91) = 1650586719047173699865498965 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v3 : rho (3^29) = 51472783023662 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v5 : rho (5^20) = 79472859700521 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v7 : rho (7^12) = 12111126301 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v11 : rho (11^9) = 2161452050 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v13 : rho (13^4) = 26521 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v17 : rho (17^1) = 16 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v19 : rho (19^1) = 18 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v23 : rho (23^7) = 3262957720 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v29 : rho (29^1) = 28 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v31 : rho (31^3) = 28860 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v37 : rho (37^1) = 36 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v41 : rho (41^1) = 40 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v43 : rho (43^1) = 42 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v47 : rho (47^2) = 2163 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v53 : rho (53^3) = 146120 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v61 : rho (61^3) = 223320 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v73 : rho (73^1) = 72 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v89 : rho (89^1) = 88 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v97 : rho (97^1) = 96 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v103 : rho (103^1) = 102 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v127 : rho (127^1) = 126 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v181 : rho (181^1) = 180 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v241 : rho (241^1) = 240 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v271 : rho (271^1) = 270 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v277 : rho (277^1) = 276 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v281 : rho (281^1) = 280 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v367 : rho (367^1) = 366 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v449 : rho (449^1) = 448 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v683 : rho (683^1) = 682 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v1013 : rho (1013^1) = 1012 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v1657 : rho (1657^1) = 1656 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v1861 : rho (1861^1) = 1860 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v2411 : rho (2411^1) = 2410 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v3221 : rho (3221^1) = 3220 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v4561 : rho (4561^1) = 4560 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v5987 : rho (5987^1) = 5986 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v7603 : rho (7603^1) = 7602 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v13421 : rho (13421^1) = 13420 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v30269 : rho (30269^1) = 30268 := by
  rw [rho_prime_pow _ _ (by norm_num)]; simp [Finset.sum_range_succ]

theorem v139921 : rho (139921^1) = 139920 := by
  rw [rho_prime_pow _ _ (bigprimes _ (by simp))]; simp [Finset.sum_range_succ]

theorem v178481 : rho (178481^1) = 178480 := by
  rw [rho_prime_pow _ _ (bigprimes _ (by simp))]; simp [Finset.sum_range_succ]

theorem v2796203 : rho (2796203^1) = 2796202 := by
  rw [rho_prime_pow _ _ (bigprimes _ (by simp))]; simp [Finset.sum_range_succ]

theorem v228511817 : rho (228511817^1) = 228511816 := by
  rw [rho_prime_pow _ _ (bigprimes _ (by simp))]; simp [Finset.sum_range_succ]

theorem N_eq : (1947793410288108579327587698415272737289992039373107522449638016140636142596276017072442826236838486130285072853813458640948347868163450516845165654669897619318450994951647517899051394662400000000000000000000 : ℕ) =
    2^91 * (3^29 * (5^20 * (7^12 * (11^9 * (13^4 * (17^1 * (19^1 * (23^7 * (29^1 * (31^3 * (37^1 * (41^1 * (43^1 * (47^2 * (53^3 * (61^3 * (73^1 * (89^1 * (97^1 * (103^1 * (127^1 * (181^1 * (241^1 * (271^1 * (277^1 * (281^1 * (367^1 * (449^1 * (683^1 * (1013^1 * (1657^1 * (1861^1 * (2411^1 * (3221^1 * (4561^1 * (5987^1 * (7603^1 * (13421^1 * (30269^1 * (139921^1 * (178481^1 * (2796203^1 * (228511817^1))))))))))))))))))))))))))))))))))))))))))) := by norm_num

/-- Wechsler's 5-imperfect number: N = 5 · f(N). -/
theorem five_imperfect :
    ((1947793410288108579327587698415272737289992039373107522449638016140636142596276017072442826236838486130285072853813458640948347868163450516845165654669897619318450994951647517899051394662400000000000000000000 : ℕ) : ℤ) =
      5 * rho 1947793410288108579327587698415272737289992039373107522449638016140636142596276017072442826236838486130285072853813458640948347868163450516845165654669897619318450994951647517899051394662400000000000000000000 := by
  rw [N_eq, rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num),
    rmul (by norm_num)]
  rw [v2, v3, v5, v7, v11, v13, v17, v19, v23, v29, v31, v37, v41, v43, v47, v53, v61, v73, v89, v97, v103, v127, v181, v241, v271, v277, v281, v367, v449, v683, v1013, v1657, v1861, v2411, v3221, v4561, v5987, v7603, v13421, v30269, v139921, v178481, v2796203, v228511817]
  norm_num
