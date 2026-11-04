/-
OEIS A182089. Conjecture: N = (330k+7)(660k+13)(990k+19)(1980k+37) is a Carmichael number if (but not only if) all
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

def N (k : Int) : Int := (330 * k + 7) * (660 * k + 13) * (990 * k + 19) * (1980 * k + 37)

theorem korselt_1 (k : Int) : N k - 1 = (330 * k + 6) * (1293732000 * k^3 + 78408000 * k^2 + 1583670 * k + 10662) := by unfold N; grind
theorem dvd_1 (k : Int) : (330 * k + 6) ∣ N k - 1 := ⟨_, korselt_1 k⟩
theorem korselt_2 (k : Int) : N k - 1 = (660 * k + 12) * (646866000 * k^3 + 39204000 * k^2 + 791835 * k + 5331) := by unfold N; grind
theorem dvd_2 (k : Int) : (660 * k + 12) ∣ N k - 1 := ⟨_, korselt_2 k⟩
theorem korselt_3 (k : Int) : N k - 1 = (990 * k + 18) * (431244000 * k^3 + 26136000 * k^2 + 527890 * k + 3554) := by unfold N; grind
theorem dvd_3 (k : Int) : (990 * k + 18) ∣ N k - 1 := ⟨_, korselt_3 k⟩
theorem korselt_4 (k : Int) : N k - 1 = (1980 * k + 36) * (215622000 * k^3 + 13068000 * k^2 + 263945 * k + 1777) := by unfold N; grind
theorem dvd_4 (k : Int) : (1980 * k + 36) ∣ N k - 1 := ⟨_, korselt_4 k⟩
