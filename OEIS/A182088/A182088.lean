/-
OEIS A182088. Conjecture: N = (30k-29)(60k-59)(90k-89)(180k-179) is a Carmichael number if (but not only if) all
its factors are prime (k ≥ 1).

Argument (Chernick-type family). For each factor f(k), f(k) - 1 divides N(k) - 1
as polynomials in k with an integer quotient. If all factors are prime, they
are distinct (different values for the allowed k), so N is squarefree with
f - 1 | N - 1 for every prime factor f: Korselt's criterion makes N a
Carmichael number.

Checked here (core Lean, `grind` ring normalisation): the polynomial
identities N(k) - 1 = (f(k) - 1) * Q(k) for every factor, for all integers k.
Not checked here: Korselt's criterion (squarefree n with p - 1 | n - 1 for all
primes p | n is a Carmichael number), which needs Fermat's little theorem.
-/

def N (k : Int) : Int := (30 * k - 29) * (60 * k - 59) * (90 * k - 89) * (180 * k - 179)

theorem korselt_1 (k : Int) : N k - 1 = (30 * k - 30) * (972000 * k^3 - 2851200 * k^2 + 2787810 * k - 908598) := by unfold N; grind
theorem dvd_1 (k : Int) : (30 * k - 30) ∣ N k - 1 := ⟨_, korselt_1 k⟩
theorem korselt_2 (k : Int) : N k - 1 = (60 * k - 60) * (486000 * k^3 - 1425600 * k^2 + 1393905 * k - 454299) := by unfold N; grind
theorem dvd_2 (k : Int) : (60 * k - 60) ∣ N k - 1 := ⟨_, korselt_2 k⟩
theorem korselt_3 (k : Int) : N k - 1 = (90 * k - 90) * (324000 * k^3 - 950400 * k^2 + 929270 * k - 302866) := by unfold N; grind
theorem dvd_3 (k : Int) : (90 * k - 90) ∣ N k - 1 := ⟨_, korselt_3 k⟩
theorem korselt_4 (k : Int) : N k - 1 = (180 * k - 180) * (162000 * k^3 - 475200 * k^2 + 464635 * k - 151433) := by unfold N; grind
theorem dvd_4 (k : Int) : (180 * k - 180) ∣ N k - 1 := ⟨_, korselt_4 k⟩
