# NT F10.2: a solution of 2^n ≡ 4 (mod n) with n ≡ 9 (mod 10)

**Source.** R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer 2004, F10 (residues of powers of two).
Paraphrase: Benkoski asked for a solution of 2^n ≡ 4 (mod n) whose last decimal digit is not 7; Zhang Ming-Zhi
(Sichuan Daxue Xuebao 27 (1990) 130-131) gave solutions with n ≡ 1 and 3 (mod 10) and asked whether there is one with
n ≡ 9 (mod 10).

**Result.** Yes. n = 1210344599 = 73 · 337 · 49199 has n ≡ 9 (mod 10) and 2^n ≡ 4 (mod n), and it is the smallest
such n. It is term number 26 of Max Alekseyev's complete list of odd solutions below 10^14 (OEIS
[A173572](https://oeis.org/A173572), b-file of 2012), which contains 35 solutions ≡ 9 (mod 10).

**Argument.** Direct computation: 2^1210344599 mod 1210344599 = 4. Minimality: exhaustive search over
n ≡ 9 (mod 10), n ≤ 1210344599.

**Evidence.**
- Lean (core): [`F10_2.lean`](F10_2.lean): `F10_2_witness : ∃ n, n % 10 = 9 ∧ 2 ^ n % n = 4` with n = 1210344599
  (modular exponentiation by squaring `powMod`, proved equal to `2 ^ n % n` by `powMod_eq`), and the factorization.
  Check: `tools/leancheck.sh`, exit 0; axioms propext, Quot.sound. No `native_decide`.
- [`certificate/benkoski.c`](certificate/benkoski.c): exhaustive search, see [`certificate/README.md`](certificate/README.md).
- Outside Lean: minimality (C search; agrees with the A173572 b-file).

**Review level.** `lean-witness`.

**Prior art.** Checked 2026-11-06. OEIS A173572 (odd n with 2^n ≡ 4 mod n; Alekseyev's b-file of all terms below
10^14, 2012) contains 1210344599, 8369326319, 10915386649, ...; nobody seems to have connected it to the question
in Guy (the book's 2004 edition and Zhang's 1990 note predate the list). Rotkiewicz (Math. Comp. 43 (1984) 271-272)
proved there are infinitely many odd solutions. Not in google-deepmind/formal-conjectures.
