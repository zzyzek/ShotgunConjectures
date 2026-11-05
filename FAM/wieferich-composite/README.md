# Composite c with 2^(c-1) ≡ 1 (mod c^2) (FAM-wieferich-composite)

## Source

Wikipedia, List of unsolved problems in mathematics (number theory, prime numbers): is there a
composite c with 2^(c-1) ≡ 1 (mod c^2)? Such c are called base-2 Wieferich pseudoprimes
(OEIS A001220 comments, A240719). Conjecture (T. Ordowski, OEIS A001220, 2016): none exist.

## Reading

c ≥ 2 composite; the congruence is in ℕ (`Nat.ModEq`). The question is open and depends on
unknown Wieferich primes (p with 2^(p-1) ≡ 1 mod p^2); the known ones are 1093 and 3511, and
PrimeGrid (2022) showed any other exceeds 2^64.

## Result

Weaker results, all checked in Lean (`wieferich_composite_mathlib.lean`):

1. Cofactor lemma (`wief_cofactor`). If 2^(c-1) ≡ 1 (mod c^2) and c = p^k m with p prime,
   k ≥ 1, m ≥ 1, then 2^(p-1) ≡ 1 and 2^(m-1) ≡ 1 (mod p^(2k)).
2. Every prime factor p of a solution is a Wieferich prime (`wief_prime_factor`), and the order of
   2 mod p^2 divides c - 1 (`wief_orderOf_dvd`).
3. A repeated prime factor p needs 2^(p-1) ≡ 1 (mod p^4) (`wief_sq_factor`); 1093 and 3511 fail
   this, so neither 1093^2 nor 3511^2 divides a solution.
4. No c = 1093^a 3511^b with a + b ≥ 2 is a solution (`wief_no_1093_3511`).
5. The primes P with P^2 ∣ 2^1092 - 1 are exactly 3, 7, 13, 1093 (`sq_dvd_two_pow_1092`).
6. No c = 1093^a P^k (P ≠ 1093 prime, a, k ≥ 1) is a solution (`wief_no_1093_prime_power`).
   This holds for every prime P, including P > 2^64, without the PrimeGrid search.

Consequence (outside Lean, uses PrimeGrid): a solution has a prime factor P > 2^64, is not
1093·P^k, and if it is 3511·P^k then P^2 ∣ 2^3510 - 1. So a solution exceeds 3511·2^64 ≈ 6.5·10^22
unless it is a prime power P^k (k ≥ 2) of a prime with 2^(P-1) ≡ 1 (mod P^(2k)).

## Argument

Let n = p^(2k). Then n ∣ c^2, so 2^(c-1) ≡ 1 (mod n); also 2^φ(n) ≡ 1 with
φ(n) = p^(2k-1)(p-1) (p = 2 is impossible: 2^(c-1) would be ≡ 1 modulo an even number).
Hence 2^g ≡ 1 with g = gcd(c-1, φ(n)). Since p ∣ c, p ∤ c-1, so g is coprime to p and g ∣ p-1.
As p ≡ 1 (mod g), c = p^k m ≡ m (mod g), and c ≡ 1 (mod g), so g ∣ m-1. Both claims of (1)
follow. (2) is k = 1; (3) is k = 2. For (4): a ≥ 2 or b ≥ 2 contradicts (3)
(2^1092 ≢ 1 mod 1093^4, 2^3510 ≢ 1 mod 3511^4); a = b = 1 gives, by (1) with p = 1093, m = 3511,
2^3510 ≡ 1 (mod 1093^2), false (ord = 364 ∤ 3510). For (6): a ≥ 2 contradicts (3); for a = 1,
(1) with p = P, m = 1093 gives P^2 ∣ 2^1092 - 1, so P ∈ {3, 7, 13} by (5), and none of these is a
Wieferich prime, contradicting (2).
(5): 2^1092 - 1 = 3^2 · 5 · 7^2 · 13^2 · … · 1093^2 · … (45 distinct primes, largest 37 digits;
the full list is `fs1092` in the Lean file). Lean checks the product, a Pratt certificate for every
prime, and that only 3, 7, 13, 1093 have exponent ≥ 2; a general lemma (`sq_dvd_factorsProd`) turns
P^2 ∣ ∏ q_i^(e_i) into P = q_i with e_i ≥ 2.

## Evidence

- `wieferich_composite_mathlib.lean`: all theorems above. Checked with `tools/leancheck-mathlib.sh`:
  OK, zero warnings, axioms ⊆ {propext, Classical.choice, Quot.sound}, no sorry, no native_decide.
  Large powers are evaluated through the library's `powMod` and `decide +kernel`.
- `certificate/factor1092.gp` (PARI/GP; cyclotomic and Aurifeuillian pieces, each ≤ 144 bits)
  produced `certificate/factor1092.out`; `certificate/gen_factors1092.py` turns it into the Lean
  factor list and Pratt certificate (via `tools/pratt_cert.py`). Lean re-checks everything, so GP
  and sympy are not trusted.
- `certificate/status3510.gp`: quick survey of 2^3510 - 1 (see obstacle below).
- Outside Lean: the PrimeGrid bound 2^64 used only in the "Consequence" paragraph.

## Review level

lean-proof for (1)–(6).

## Prior art (checked 2026-11-05)

- OEIS A240719 (F. Fröhlich, 2015 comment): a composite solution must be a product of Wieferich
  primes, and products 1093^x 3511^y are excluded (x or y > 1 by a PARI check of
  2^(p-1) mod p^(2k), x = y = 1 because 3837523 is not a base-2 pseudoprime). So (2)–(4) are
  **known**. A240719 also records that any further term exceeds 1.2·10^17 (Greathouse, 2014).
- OEIS A001220 comments (Ordowski 2016 conjecture; Fröhlich 2019): a base-2 Wieferich pseudoprime
  must be a base-2 Fermat pseudoprime with all prime factors Wieferich.
- google-deepmind/formal-conjectures: `FormalConjectures/Wikipedia/WieferichPrime.lean` has
  Wieferich-prime statements (infinitely many, only 1093/3511, base 47); no composite-c statement.
  No Lean proof of (2)–(6) found there.
- ~/claude/openai-math/repo (CONTENTS.md, lean/): no Wieferich or Wieferich-pseudoprime item.
- Not consulted directly: Ribenboim's books, Agoh–Dilcher–Skula (1997) on Fermat quotients,
  Montgomery (1993) on Wieferich primes among Cunningham-table factors.
- New or known: (2)–(4) known. The cofactor form (1) with exponent m - 1 and the exclusion (6) of
  every 1093·P^k were not found in the sources above. (6) amounts to "2^1092 - 1 has no Wieferich
  prime factor other than 1093", which may be implicit in Wieferich searches over Cunningham-table
  factors; treat (6) as possibly new as an explicit statement, and new as a Lean proof.

## Obstacles

- 3511·P^k: (1) gives P^2 ∣ 2^3510 - 1, which needs the full factorization of 2^3510 - 1. A quick
  pass (trial division by primes ≡ 1 mod d below 2^26) leaves composite cofactors of 173–820 bits
  in Φ_d(2) for d = 351, 585, 702, 1170, 1755 (d = 3510 not reached in 300 s). Not attempted
  further (Cunningham-table data not checked).
- 1093·3511·P^k: P^2 ∣ 2^3837522 - 1, out of reach.
- Prime powers P^k (k ≥ 2): need a prime with 2^(P-1) ≡ 1 (mod P^4); no structural handle.


## Extension: Base-2 Wieferich pseudoprimes of the form 3511^b · P^k (FAM-wieferich-composite, extension)

## Source

Wikipedia, List of unsolved problems in mathematics (number theory, prime numbers): is there a
composite c with 2^(c-1) ≡ 1 (mod c^2)? (OEIS A001220 comments, A240719; Ordowski 2016
conjectures there is none.) This directory extends `FAM/wieferich-composite/`, which excluded
every c = 1093^a · P^k.

## Reading

As in the pilot: c ≥ 2, congruence in ℕ. P is any prime other than 3511, with no size bound
(in particular P > 2^64 is allowed, so the PrimeGrid search is not used).

## Result

1. The full factorization of 2^3510 - 1 (67 distinct primes, largest 146 digits) has exactly two
   primes with exponent ≥ 2, namely 3^4 and 3511^2. So the primes P with P^2 ∣ 2^3510 - 1 are
   3 and 3511 (`sq_dvd_two_pow_3510`).
2. No c = 3511^b · P^k (b, k ≥ 1, P ≠ 3511 prime) satisfies 2^(c-1) ≡ 1 (mod c^2)
   (`wief_no_3511_prime_power`).

In Lean both are proved under one hypothesis, the primality of `bigP146` (146 digits, a factor
of Φ_1755(2)). All 66 other prime factors (largest 126 digits) are Pratt-certified in Lean.
Outside Lean, PARI/GP `isprime(p, 2)` (APRCL) proves `bigP146` prime, and factordb lists it with
status "P" (proven prime).

Combined with the pilot (`wief_no_1093_prime_power`, `wief_no_1093_3511`, `wief_prime_factor`,
`wief_sq_factor`): a composite solution c is not of the form p^a · P^k with p ∈ {1093, 3511}
and P prime. So c either

- has at least three distinct prime factors, all Wieferich primes, or
- has exactly two distinct prime factors, both Wieferich primes other than 1093 and 3511
  (so both > 2^64 by PrimeGrid, outside Lean), or
- is a prime power P^k, k ≥ 2, with 2^(P-1) ≡ 1 (mod P^(2k)) (P > 2^64 by PrimeGrid, and
  P ∉ {1093, 3511} by `wief_sq_factor`).

Side result: Ordowski (OEIS A001220, 2014) asked for primes q ≥ p with q^2 ∣ 2^(p-1) - 1. For
p = 1093 (pilot) and p = 3511 (here) the only such q is p itself.

## Argument

(2) b ≥ 2: 3511^2 ∣ c forces 2^3510 ≡ 1 (mod 3511^4) (pilot's `wief_sq_factor`), which is false.
b = 1: the cofactor lemma (`wief_cofactor`, from the pilot) with p = P, m = 3511 gives
2^3510 ≡ 1 and 2^(P-1) ≡ 1 (mod P^(2k)). So P^2 ∣ 2^3510 - 1 and P is a Wieferich prime. By (1),
P = 3 (2^2 ≢ 1 mod 9) or P = 3511 (excluded).

(1) 2^3510 - 1 = ∏_{d ∣ 3510} Φ_d(2) (32 divisors). Lean checks that the product of the listed
prime powers equals 2^3510 - 1, that the listed primes are distinct, that each is prime (Pratt
certificate, or the hypothesis on `bigP146`), and that only 3 and 3511 have exponent ≥ 2;
`sq_dvd_factorsProd` turns P^2 ∣ ∏ q_i^(e_i) into P = q_i with e_i ≥ 2.

Factorization per d (digits of Φ_d(2) | digits of its prime factors; "^2" marks a square):

| d | digits | factor digits | source |
|---|---|---|---|
| 1, 2, 3, 5, 6, 9, 10, 13, 15, 18, 26, 27, 30, 39, 45, 54, 65, 78, 90 | ≤ 15 | ≤ 15 | PARI `factor` |
| 117 | 22 | 10 5 4 3 | PARI `factor` |
| 130 | 15 | 7 6 3 | PARI `factor` |
| 135 | 22 | 14 6 3 | PARI `factor` |
| 195 | 30 | 30 | PARI `factor` |
| 234 | 22 | 22 | PARI `factor` |
| 270 | 22 | 15 5 3 | PARI `factor` |
| 390 | 29 | 24 6 | PARI `factor` |
| 351 | 66 | 21 17 15 8 6 | factordb (FF) |
| 585 | 87 | 40 21 18 10 | factordb (FF) |
| 702 | 66 | 41 25 | factordb (FF) |
| 1170 | 87 | 40 29 11 5 4 | factordb (FF) |
| 1755 | 261 | **146** 63 20 19 7 4^2 (= 3511^2) | factordb (FF) |
| 3510 | 261 | **126** 58 22 18 14 9 7 7 5 | factordb (FF) |

3 occurs in Φ_2, Φ_6, Φ_18, Φ_54 (total 3^4). Full per-d table: `certificate/3511/data/table3510.txt`.

## Evidence

- `wieferich_composite_3511_mathlib.lean`, checked with `tools/leancheck-mathlib.sh` (12 s): OK, zero
  warnings, no sorry, no native_decide. Axioms ⊆ {propext, Classical.choice, Quot.sound}.
  Theorems:
  - `factorsProd_3510 : factorsProd fs3510 = 2 ^ 3510 - 1`
  - `primes_3510_small : ∀ n ∈ (fs3510.map Prod.fst).filter (· ≠ bigP146), n.Prime`
    (Pratt certificates for 66 primes, up to 126 digits)
  - `sq_dvd_two_pow_3510 (h146 : bigP146.Prime) (P : ℕ) (hP : P.Prime)
    (h : P ^ 2 ∣ 2 ^ 3510 - 1) : P = 3 ∨ P = 3511`
  - `wief_no_3511_prime_power (h146 : bigP146.Prime) (b k P : ℕ)
    (hP : P.Prime) (hP3511 : P ≠ 3511) (hb : 1 ≤ b) (hk : 1 ≤ k) :
    ¬ 2 ^ (3511 ^ b * P ^ k - 1) ≡ 1 [MOD (3511 ^ b * P ^ k) ^ 2]`
  - helpers `wief_cofactor`, `wief_sq_factor`, `sq_dvd_factorsProd` (copied from the pilot so
    the file is standalone), `wief_not_3511_sq`, `not_modEq_3511_4`, `nodup_3510`,
    `primes_3510`.
- Outside Lean: primality of `bigP146`. Its p - 1 = 2^5·3^5·5·11·13·269·2957·795997·C with C a
  422-bit composite (unfactored on factordb; also p + 1 = 2·(485-bit composite)), so neither a
  Pratt nor a Pocklington (F ≥ √p, about 243 bits) certificate is available.
  `certificate/3511/data/isprime_big.log` records PARI `isprime(p, 2)` = 1 (APRCL) for both large
  primes and which Φ_d(2) each divides.
- The 126-digit factor of Φ_3510(2) has p - 1 = 2^3·3^3·5^2·13·17·173·C' with C' a 391-bit
  composite (unfactored on factordb). ECM stage 1 (`ecm_stage1.gp`, B1 = 10^5, 250 curves) split
  C' into 228464363 · 34268416234523 · 1031876751151739179 · 11505823460373003803959 and a
  185-bit prime (`data/ecm_idx2_b1e5_s0.log`, `data/hints.txt`), which completes its Pratt
  certificate; p - 1 of the smaller certificate primes is factored by PARI `factor`.
- `certificate/3511/phi3510.gp` → `data/phi3510.txt` (Φ_d(2) for all d ∣ 3510).
- `certificate/3511/data/factordb/phi_<d>.json`: factordb API replies (2026-11-05) for
  d = 351, 585, 702, 1170, 1755, 3510, all status "FF". `build_factors.py` extracts them to
  `data/factors3510_claimed.txt`; `factor3510.gp` checks every claimed factor with `isprime`,
  each claimed piece's product against Φ_d(2), factors the small pieces, checks the total
  product against 2^3510 - 1, and writes `data/factor3510.out` ("p e" lines).
- `gen_factors3510.py` (with `tools/pratt_cert.py`, factoring p - 1 by PARI after dividing out
  `data/hints.txt`) emits `fs3510` and `cert3510` (`data/lean_factors3510.txt`). Lean re-checks everything, so factordb, GP and sympy are not
  trusted except for the two primality facts above.
- `pm1_probe.gp`, `pm1_partial.gp`, `ecm_try.gp`, `ecm_stage1.gp`: attempts to factor p - 1 of
  the two big primes (see Obstacles); `data/factordb/pm1_*.json`, `pp1_*.json` are the factordb
  replies for p ± 1.

## Review level

lean-proof for (1) and (2) conditional on one explicit primality hypothesis (`bigP146`), which
is rechecked outside Lean (PARI APRCL, factordb).

## Prior art (checked 2026-11-05)

- OEIS A240719: Fröhlich (2015) proves every prime factor is Wieferich and excludes
  1093^x 3511^y; Greathouse (2014): further terms > 1.2·10^17. Nothing on 3511·P^k.
- OEIS A001220: Ordowski (2016) conjecture; Fröhlich (2019) necessary conditions; Gill (2013)
  and Alekseyev (2014): a prime q with q^2 ∣ 2^(p-1) - 1, q ≥ p, must be Wieferich; Ordowski
  (2014) asked for such q. PrimeGrid completed 2^64 (Greathouse 2024 comment). Nothing on
  square factors of 2^3510 - 1 specifically.
- Agoh, Dilcher, Skula, Fermat quotients for composite moduli, J. Number Theory 66 (1997) 29–50:
  defines Wieferich numbers via the Euler quotient, a^φ(m) ≡ 1 (mod m^2) (definition as quoted
  by Klaška, JIS 25 (2022)). That is a different condition from 2^(m-1) ≡ 1 (mod m^2); the
  paper itself was not read (paywalled).
- google-deepmind/formal-conjectures: `Wikipedia/WieferichPrime.lean` has Wieferich-prime
  statements, no composite-c statement (as checked for the pilot, same date).
- New or known: the factorization of 2^3510 - 1 is known (factordb, complete). The exclusion
  of 3511·P^k for all primes P was not found stated anywhere; it follows quickly once the
  factorization is in hand, so it is likely folklore-level but not written down. New as a Lean
  proof (conditional on one primality).

## Obstacles

- Lean primality of `bigP146` (d = 1755, 146 digits): needs about 181 more bits of p - 1
  factored for Pocklington (not in the library; would need a short Lean proof) or all of it for
  Pratt, or an ECPP checker in Lean. On the 422-bit cofactor, PARI `factor` (280 s), ECM stage 1
  with B1 = 10^5 (250 curves) and B1 = 10^6 (300 curves, `ecm_more.sh`, logs
  `data/ecm_idx1_*.log`) found nothing, so it likely has no factor below about 25 digits.
  Next: GMP-ECM with stage 2 or NFS on the 127-digit cofactor (CPU-days).
- Three or more distinct Wieferich prime factors (e.g. 1093·3511·P^k, needing square factors of
  2^3837522 - 1) and prime powers P^k remain open, as in the pilot.
