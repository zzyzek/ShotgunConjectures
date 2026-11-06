# OEIS A171949: P-positions of Mark-4 versus A217319

**Source.** OEIS [A171949](https://oeis.org/A171949), P-positions for the game Mark-4 (offset 1, a(1) = 0).
Formula line: "Conjecture: For n>=2, a(n) = A217319(n-1)." (V. Shevelev, Mar 18 2013; still a conjecture in
revision #26 of May 30 2026, checked 2026-11-06.) (OEIS text, CC BY-SA 4.0.)

**Result.** True; known (Fraenkel 2012). This is the same statement as the conjecture in A217319
("a(n) = A171949(n+1)"), settled and proved in core Lean in [`../A217319/`](../A217319/README.md):
`A217319_main` says n is a P-position of Mark-4 iff n = 0 or n = 4^(2k+1)·m with 4 ∤ m. Listing that set in
increasing order gives 0 followed by the terms of A217319 in order, which is a(n) = A217319(n-1) for n ≥ 2.

**Evidence, review level, prior art.** See [`../A217319/README.md`](../A217319/README.md) (`lean-proof`).
Outside Lean, beyond what is listed there: the step from the set equality to the index shift of the two
increasing listings (immediate).
