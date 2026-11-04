/-
OEIS A100682 (floor of 4th root of pentatope numbers). Conjecture (Greathouse,
2012): floor((n - 3/2)/24^(1/4)) equals floor(C(n,4)^(1/4)) except for
n in {0, 1, 6, 17, 2403, 5318}. False: n = 634027531 is another exception
(OEIS index 634027528, since the entry defines a(n) = floor(C(n+3,4)^(1/4))).

Checked here: the integer facts at n = 634027531.
Not checked here: the real-number step
  b ≤ (n - 3/2)/24^(1/4)  ⇔  384·b^4 ≤ (2n - 3)^4   (b, n - 3/2 ≥ 0),
i.e. monotonicity of x ↦ x^4 on nonnegative reals.
-/

def n0 : Nat := 634027531
def c4 : Nat := n0 * (n0 - 1) * (n0 - 2) * (n0 - 3) / 24

theorem c4_exact : n0 * (n0 - 1) * (n0 - 2) * (n0 - 3) % 24 = 0 := by decide

/-- floor(C(n0,4)^(1/4)) = 286454272 -/
theorem root_lo : 286454272 ^ 4 ≤ c4 := by decide
theorem root_hi : c4 < 286454273 ^ 4 := by decide

/-- floor((n0 - 3/2)/24^(1/4)) = 286454273, via 384·b^4 ≤ (2·n0 - 3)^4 < 384·(b+1)^4 -/
theorem form_lo : 384 * 286454273 ^ 4 ≤ (2 * n0 - 3) ^ 4 := by decide
theorem form_hi : (2 * n0 - 3) ^ 4 < 384 * 286454274 ^ 4 := by decide

/-- The exceptions below 6000 are exactly the stated ones (checked in Python, not here). -/
theorem differ : (286454272 : Nat) ≠ 286454273 := by decide
