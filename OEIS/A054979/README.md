# OEIS A054979: "every e-perfect number is divisible by 36" is equivalent to the open Straus-Subbarao question

**Source.** OEIS [A054979](https://oeis.org/A054979) (e-perfect numbers, sum of exponential
divisors = 2k), comment by Jon Perry (Nov 13 2012): "Conjecture: Every e-perfect number is
divisible by 36, see A219016." (OEIS text, CC BY-SA 4.0.)

**Result.** Partial; the claim is equivalent to a known open problem.
- 4 | n holds for every e-perfect n (from Straus-Subbarao, below).
- 9 | n for every e-perfect n is equivalent to: no e-perfect number is coprime to 3. That is the
  question raised by Straus and Subbarao; Fabrykowski and Subbarao showed that an e-perfect
  number not divisible by 3 exceeds 10^664 (with further necessary conditions), and
  Lelechenko (arXiv:1405.7597, 2014) still lists it as open. No later resolution found.
So the conjecture is open, and it is exactly the "3 does not divide" question.

**Argument.** σ_e is multiplicative with σ_e(p^a) = sum_{d | a} p^d, and σ_e(p) = p.
So if p || n then σ_e(n)/n = σ_e(n/p)/(n/p): n is e-perfect iff n/p is.
(i) Straus-Subbarao (1974): no odd e-perfect numbers. Hence n is even, and if 2 || n then n/2
would be an odd e-perfect number, so 4 | n.
(ii) If 3 || n then n/3 is e-perfect and coprime to 3. So "9 | n for all e-perfect n" holds iff
"3 | n for all e-perfect n", which is the open question. Conversely a counterexample to the
open question is itself a counterexample to the conjecture.
The b-file (10000 terms, Eldar) has every term divisible by 36 (checked 2026-11-06).

**Evidence.** Hand argument above; citations. No Lean (the odd-e-perfect theorem is not
formalised). Outside Lean: everything.

**Review level.** `rechecked` for the reduction, `agent` for the cited theorems.

**Prior art.** E. G. Straus, M. V. Subbarao, On exponential divisors, Duke Math. J. 41 (1974)
465-471 (no odd e-perfect numbers); J. Fabrykowski, M. V. Subbarao, On e-perfect numbers not
divisible by 3, Nieuw Arch. Wisk. (4) 4 (1986) 165-173 (n > 10^664); A. V. Lelechenko,
arXiv:1405.7597, Section on e-infinity-perfect numbers (states it open). Searched 2026-11-06:
web, OEIS A054979/A219016, google-deepmind/formal-conjectures HEAD 2026-11-06 (no entry),
otoi-lab/oeis-lean-proofs (no entry).
