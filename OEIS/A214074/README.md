# OEIS A214074: a(n) = 3 is not the residue class n ≡ 121 (mod 330)

**Source.** OEIS [A214074](https://oeis.org/A214074), least m > 0 such that 2^n − m and 3^n − m are
relatively prime. Comment: "Conjecture: a(n) = 3 if and only if n = 330*k-209 for some k>=1."
(OEIS text, CC BY-SA 4.0.)

**Result.** False in both directions.
- n₁ = 3438721 = 330·10421 − 209 has a(n₁) = 4 (Lean proves a(n₁) ≥ 4).
- n₂ = 1186095 ≡ 75 (mod 330) has a(n₂) = 3 (Lean proves a(n₂) ≥ 3; the gcd for m = 3 is from PARI/GP).
The conjecture holds for all n ≤ 40000 (`certificate/scan.out`).

**Argument.** a(n) ≥ m + 1 when some prime divides both 2^n − j and 3^n − j for each j ≤ m.
- q | gcd(2^n − 1, 3^n − 1) iff ord_q 2 | n and ord_q 3 | n. For q = 23 both orders are 11, so 11 | n gives a(n) ≥ 2.
- q | gcd(2^n − 2, 3^n − 2) (q odd) iff 2^(n−1) ≡ 1 and 3^n ≡ 2 (mod q). This needs ord_q 2 | ord_q 3 and
  log₃ 2 ≡ 1 (mod ord_q 2), and then fixes n mod ord_q 3. Among q < 3·10⁶ only q = 331 (n ≡ 121 mod 330) and
  q = 1210483 (n ≡ 379107 mod 403494) qualify (`certificate/p2.out`). The class 121 mod 330 is the q = 331 class,
  and 11 | n there, which explains the observed pattern.
- q | gcd(2^n − 3, 3^n − 3) (q > 3) iff 3^(n−1) ≡ 1 and 2^n ≡ 3 (mod q). q = 487891 gives the class
  n ≡ 23491 (mod 487890), which meets 121 mod 330 in n ≡ 3438721 (mod 5366790). So a(n) ≥ 4 on that class.
- n₂ = 1186095 is in the q = 1210483 class, 88681 | gcd(2^n₂ − 1, 3^n₂ − 1), and gcd(2^n₂ − 3, 3^n₂ − 3) = 1
  (PARI/GP), so a(n₂) = 3 while n₂ ≡ 75 (mod 330). Other n in the same class with a(n) = 3: 1589589, 1993083,
  2396577, 3203565, 4414047, 5221035 (`certificate/cex.out`).

**Evidence.**
- Lean (Mathlib + `OpenProblemsLib.PowMod`): [`A214074_mathlib.lean`](A214074_mathlib.lean). `A214074` is the
  entry's definition (`Nat.find`, integer gcd). `A214074_if_false`: not every n = 330k − 209 has a(n) = 3.
  `A214074_n1_ge4`, `A214074_n2_ge3`, `A214074_n2_not_form`. Residues by square-and-multiply (`powMod`) and
  `decide +kernel`. Axioms propext, Classical.choice, Quot.sound; zero warnings.
- Outside Lean: gcd(2^n₂ − 3, 3^n₂ − 3) = 1 for n₂ = 1186095 (numbers of about 1.9·10⁶ bits; PARI/GP
  `gcd`, `certificate/w.gp`), which turns a(n₂) ≥ 3 into a(n₂) = 3 and so refutes the "only if" direction.
- `certificate/scan.gp` (a(n) for n ≤ 40000), `classes.gp`, `p2.gp` (prime classes for m = 2 and m = 3),
  `cex.gp` (counterexamples), `w.gp` (witness primes and the m = 3 gcd).

**Review level.** `lean-witness` ("if" direction refuted in Lean; "only if" refuted with one gcd outside Lean).

**Prior art.** Checked 2026-11-06: the entry still lists the comment as a conjecture; terms in the b-file stop
at n = 1000. Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs. No other source found.
