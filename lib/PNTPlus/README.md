# PNTPlus: vendored PrimeNumberTheoremAnd (prime number theorem)

Source: [AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
(PNT+), commit `127b50e33f6033e2147921167a117af96d9ba4ea` (2026-10-19, "bump deps to v4.35.0").
License: Apache License 2.0 (copy in `LICENSES/Apache-2.0.txt`). Copyright the PNT+ contributors.
PNT+ pins Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0), the revision this repo
checks against, so no version port was needed.

## Contents

The import closure of `StrongPNT` (StrongPNT.lean) and of the `Consequences` theorems, 18 files,
22 001 lines upstream: Auxiliary, MellinCalculus, Sobolev, Fourier, Rectangle,
ResidueCalcOnRectangles, EulerMaclaurin, ZetaBounds, ZetaConj, SmoothExistence, MediumPNT,
StrongPNT, Defs, Wiener, Consequences and three `Mathlib/` helper files.

Theorems used by this repo, with their axioms (`#print axioms`, 2026-11-07):

| theorem | statement | used by |
|---|---|---|
| `StrongPNT` | ∃ c > 0, ψ(x) − x = O(x exp(−c √log x)) | OEIS-A139043 |
| `chebyshev_asymptotic` | θ ~ x | OEIS-A139043 |
| `mu_pnt_alt` | Σ_{n<x} μ(n)/n = o(1) | OEIS-A097945 |
| `nth_prime_asymp`, `pn_pn_plus_one` | p_n ~ n log n, p_{n+1}/p_n → 1 | OEIS-A119659 |

All of these, and `MediumPNT`, `WeakPNT''`, `pi_alt`, `pi_asymp`, `prime_between`, `mu_pnt`,
`lambda_pnt`, depend only on `propext`, `Classical.choice`, `Quot.sound`.

## Changes from upstream

Every file carries a header comment saying it is modified. The changes are mechanical:

1. LeanArchitect blueprint metadata removed: `import Architect`, every `@[blueprint ...]`
   attribute and every `blueprint_comment /-- ... -/` block
   (`tools/pntplus_strip_blueprint.py`; it only deletes text, which was checked by diff).
2. `import PrimeNumberTheoremAnd.X` renamed to `import PNTPlus.X` (module paths only;
   namespaces and declaration names are unchanged, most are at the root namespace).
3. Wiener.lean: the three declarations `prelim_decay_2` and `prelim_decay_3` (both `sorry`
   upstream) and `decay_alt` (their only user) removed. Nothing else in the closure uses them.

## Building

`tools/buildlib.sh` compiles `PNTPlus/*` first (list `PNTPLUS` in the script, dependency
order), then `OpenProblemsLib/*`. Cost on this machine (2026-11-07): about 3 minutes wall for
the 18 files, peak 4.3 GB RSS (MediumPNT), no warnings. Import with
`import PNTPlus.Consequences` / `import PNTPlus.StrongPNT`. Root-namespace names such as
`nth_prime`, `log2_pos`, `M` can clash with other root names, so problem files put their own
declarations in a namespace.

Not included: PNT+'s IEANTN explicit-estimate files (Rosser–Schoenfeld, Dusart, Chebyshev
explicit bounds); upstream most are `sorry` or use `native_decide`.
