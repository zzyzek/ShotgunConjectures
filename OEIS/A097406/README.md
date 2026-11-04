# OEIS A097406: primitive prime factors of 2^n − 1 are ≡ 1 (mod n)

**Source.** [A097406](https://oeis.org/A097406) (largest primitive prime factor of 2^n − 1, or 1), comment:
"Conjectures: (1) For every n the highest unique prime factor is of the form kn+1. ... (2) For each composite n
many factors of the form kn+1 occur intermittently but always singly in any cofactor pair. (3) For each prime n
every factor is of the form kn+1." (OEIS text, CC BY-SA 4.0.)

**Result.** (1) and (3) are true and standard; (2) is too vague to be a mathematical statement (misstated).

**Argument.** A primitive prime factor p of 2^n − 1 divides no 2^m − 1 with m < n, so ord_p(2) = n, and
ord_p(2) | p − 1 (Fermat), so p ≡ 1 (mod n). (When a(n) = 1, as for n = 1, 6, the value 1 = 0·n + 1 also fits.)
For prime n, any prime p | 2^n − 1 has ord_p(2) | n and ord_p(2) ≠ 1, so ord_p(2) = n and again p ≡ 1 (mod n).

**Evidence.**
- Lean (Mathlib): [`A097406_mathlib.lean`](A097406_mathlib.lean) proves the full result (`A097406_part1, A097406_part3`): every primitive prime factor p of 2^n - 1 has n | p - 1, and for prime n every prime factor does; ord_p(2) = n (Mathlib `orderOf_eq_iff`, `orderOf_eq_prime`) and Fermat (`ZMod.orderOf_dvd_card_sub_one`). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- `certificate/check.py`: parts (1) and (3) for n ≤ 90 (sympy factorint).

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`A097406_mathlib.lean`](A097406_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`).
**Prior art.** Known: (1) and (3) are the textbook fact that ord_p(2) = n implies p == 1 (mod n); the entry itself already characterizes a(n) by ord_p(2) = n (J. Song, 2019). (2) is not a precise statement. [A097406](https://oeis.org/A097406) still lists them as conjectures. Searched OEIS entry, references and history. Checked 2026-11-04.
