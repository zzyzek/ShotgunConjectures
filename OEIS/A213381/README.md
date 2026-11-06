# OEIS A213381: n^n mod (n+2) — zeros and the A176003 values (parts 3–4 open)

**Source.** [A213381](https://oeis.org/A213381), "a(n) = n^n mod (n+2)." Conjectures: (1) indices of zeros are
2^(x+2)−2, x ≥ 0; (2) a(n) = n if n is in A176003 (3q − 2, q = 1 or prime); (3) every k ≥ 0 appears at least
once; (4) every k ≥ 0 appears infinitely often. Robert Israel (May 2015, in the entry) proved (1) and (2).
(OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Result.** Partial. (1) and (2) are true (Israel's proofs, formalised here). (3) and (4) are open: a(n) = k
means (−2)^{m−2} ≡ k (mod m) with m = n+2, a congruence of the same type as Graham's 1960 conjecture on
2^n ≡ k (mod n) (OEIS A036236; e.g. the least n with 2^n ≡ 3 (mod n) is 4700063497).

**Argument (1), (2).** n ≡ −2 (mod n+2), so n^n ≡ (−2)^n and (n+2) | n^n iff (n+2) | 2^n iff n+2 = 2^j with
j ≤ n, i.e. n = 2^j − 2 with j ≥ 2. For n = 3q − 2 with q prime, q ∉ {2, 3}: n ≡ 1 (mod 3) gives n^n ≡ n (mod 3);
n = 3(q−1) + 1 and Fermat give n^n ≡ n (mod q); CRT and n < 3q give n^n mod 3q = n. q = 1, 2, 3 by computation.

**Evidence.**
- Lean (Mathlib): [`A213381_mathlib.lean`](A213381_mathlib.lean): `A213381_zero_iff` (n^n % (n+2) = 0 ↔ ∃ x,
  n = 2^(x+2) − 2) and `A213381_A176003` (q = 1 or prime → (3q−2)^(3q−2) % (3q) = 3q−2). `tools/leancheck-mathlib.sh`
  exit 0, no warnings; axioms propext, Classical.choice, Quot.sound.
- Search for (3), (4) ([`certificate/a213.c`](certificate/a213.c), output `a213_1e9.out`, n < 10^9, about 4 min):
  k = 10 never occurs; k = 5 occurs only at n = 9 and n = 83294759; k = 71 first at n = 18349355; k = 107 first at
  n = 14797203. [`certificate/a213.py`](certificate/a213.py): for n < 3·10^6 every k < 200 except 10, 71, 107 occurs.
- Outside Lean: parts (3) and (4) (not proved).

**Review level.** `lean-proof` for (1) and (2).

**Prior art.** Checked 2026-11-06. (1), (2) proved in the entry (Israel 2015). For (3), (4): the analogous
question for 2^n mod n (Graham 1960, A036236) is open; no result covering (−2)^{m−2} mod m found. Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (trees at HEAD 2026-11-06).
