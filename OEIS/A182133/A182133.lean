/-
OEIS A182133. Conjecture: N = (30k+13)(90k+37)(150k+61) is a Carmichael number if (but not only if) all
its factors are prime (k ≥ 0).

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

def N (k : Int) : Int := (30 * k + 13) * (90 * k + 37) * (150 * k + 61)

theorem korselt_1 (k : Int) : N k - 1 = (30 * k + 12) * (13500 * k^2 + 11490 * k + 2445) := by unfold N; grind
theorem dvd_1 (k : Int) : (30 * k + 12) ∣ N k - 1 := ⟨_, korselt_1 k⟩
theorem korselt_2 (k : Int) : N k - 1 = (90 * k + 36) * (4500 * k^2 + 3830 * k + 815) := by unfold N; grind
theorem dvd_2 (k : Int) : (90 * k + 36) ∣ N k - 1 := ⟨_, korselt_2 k⟩
theorem korselt_3 (k : Int) : N k - 1 = (150 * k + 60) * (2700 * k^2 + 2298 * k + 489) := by unfold N; grind
theorem dvd_3 (k : Int) : (150 * k + 60) ∣ N k - 1 := ⟨_, korselt_3 k⟩
