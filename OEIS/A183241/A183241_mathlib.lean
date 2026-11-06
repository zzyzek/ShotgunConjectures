import Mathlib
import OpenProblemsLib.DworkMultinomial

/-
OEIS A183241 (P. D. Hanna, 2011): g.f. exp(Σ_{n≥1} A183240(n) x^n/n) with
A183240(n) = Σ_{partitions λ of n} (n!/Π λ_i!)^2; OEIS A182963: the same with cubes
(A183235(n) = Σ_λ (n!/Π λ_i!)^3). Both "Conjectured to consist entirely of integers."

Definitions.
* `partitionSum r n = Σ_{λ : n.Partition} (n! / Π_{x ∈ λ} x!)^r` (library
  `OpenProblemsLib.DworkMultinomial`, ℕ division, exact).
* `expCoeff b n`: coefficients of exp(Σ b(n) x^n/n) via (n+1) A(n+1) = Σ b(j+1) A(n-j).

Main theorems. `A183241_int n : ∃ z : ℤ, expCoeff (partitionSum 2) n = z`,
`A182963_int n : ∃ z : ℤ, expCoeff (partitionSum 3) n = z`.

Route: `LGp_partitionSum` (Gauss congruences of partitionSum r at every prime, from the Frobenius
congruence (x_0 + ... + x_K)^(p n) ≡ (x_0^p + ... + x_K^p)^n mod p^(1+v_p n): multinomials of
p-divisible partitions are congruent to those of the divided partition, the others vanish), then
Dwork's lemma `expCoeff_int_of_gauss`. This replaces the necklace argument of the README.
Not checked here: the recurrence as the OEIS "exp(...)" (standard reading); data agreement
(certificate/multinomial_check.py).
-/

namespace A183241

open OpenProblemsLib.Dwork OpenProblemsLib.DworkMultinomial

/-- A183240(n) = Σ_{λ ⊢ n} (n!/Π λ_i!)^2. -/
def a183240 (n : ℕ) : ℤ := partitionSum 2 n

/-- A183235(n) = Σ_{λ ⊢ n} (n!/Π λ_i!)^3. -/
def a183235 (n : ℕ) : ℤ := partitionSum 3 n

/-- A183241: exp(Σ A183240(n) x^n/n) has integer coefficients. -/
theorem A183241_int (n : ℕ) : ∃ z : ℤ, expCoeff a183240 n = z :=
  expCoeff_partitionSum_int 2 (by norm_num) n

/-- A182963: exp(Σ A183235(n) x^n/n) has integer coefficients. -/
theorem A182963_int (n : ℕ) : ∃ z : ℤ, expCoeff a183235 n = z :=
  expCoeff_partitionSum_int 3 (by norm_num) n
