# OEIS A182088: (30n-29)(60n-59)(90n-89)(180n-179) is Carmichael whenever its factors are prime

**Source.** OEIS [A182088](https://oeis.org/A182088), conjecture by Marius Coman (2012): "The number C = (30n-29)*(60n-59)*(90n-89)*(180n-179) is a Carmichael number if (but not only if) 30n-29, 60n-59, 90n-89 and 180n-179 are all four prime numbers."
(OEIS text, CC BY-SA 4.0.)

**Result.** True (for the stated range n ≥ 1).

**Argument.** Chernick-type family. For each factor f, f - 1 divides N - 1 as polynomials in the
parameter with an integer quotient (N - 1 = 180(n-1)(162000n^3-475200n^2+464635n-151433) factored over Z; the quotients are in
`certificate/korselt_poly.py` and in the Lean file). If all factors are prime they are distinct
(the linear forms take different values in the stated range), so N is squarefree, and every prime
factor f has f - 1 | N - 1. Korselt's criterion then makes N a Carmichael number.

**Evidence.**
- Lean (Mathlib): [`A182088_mathlib.lean`](A182088_mathlib.lean) proves the full result (`A182088_main`): for every n, if 30n-29, 60n-59, 90n-89, 180n-179 are prime then the product is Carmichael (`Nat.IsCarmichael`); Korselt via Mathlib, identities by `ring`. Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- [`A182088.lean`](A182088.lean): the identities N - 1 = (f - 1) Q
  for every factor, for all integers k (core Lean, `grind` ring normalisation). Outside Lean:
  Korselt's criterion (sufficiency), which needs Fermat's little theorem.
- `certificate/korselt_poly.py`: sympy division with zero remainder and integer quotients for all
  six families of this kind (A182085, A182088, A182089, A182132, A182133, A182416).

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`A182088_mathlib.lean`](A182088_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`A182088.lean`](A182088.lean) checks the parts named under Evidence.

**Prior art.** Verdict known, immediate (OEIS status conjecture; searched 2026-11-04). The product is U_4(m) with m = 5(n-1) (p(2p-1)(3p-2)(6p-5), p = 30n-29), Chernick's 1939 form. Sources: [OEIS A182088 (fetched 2026-11-04)](https://oeis.org/A182088): still says Conjecture; [J. Chernick (1939), universal form U_4(m) = (6m+1)(12m+1)(18m+1)(36m+1); see OEIS A182518](https://oeis.org/A182518): Carmichael whenever all four factors are prime, any m. Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; OEIS A182518, A391076; Google: Chernick universal form four factors.
