# OEIS A178790: integrality and the Apery-sum congruence mod p^2 are both proved (Sun; Wang-Sun)

**Source.** OEIS [A178790](https://oeis.org/A178790) (mean of (2k+1)A_k, A_k Apery numbers
A005259), comments by Zhi-Wei Sun: "Conjecture: the number a(n) = n^(-1)*Sum_{k=0..n-1}(2*k+1)*A_k
is always an integer" and "Conjecture: If p=5,7 (mod 8) is a prime then sum_{k=0}^{p-1}A_k=0
(mod p^2); if p=1,3 (mod 8) is a prime greater than 3 and p=x^2+2y^2 with x,y integers then
sum_{k=0}^{p-1}A_k=4x^2-2p (mod p^2)." (OEIS text, CC BY-SA 4.0.)

**Result.** Both parts are theorems.
- Integrality: Z.-W. Sun, Arithmetic properties of Apery numbers and central Delannoy numbers,
  arXiv:1006.2776 (noted in the entry, Jun 17 2010), via
  a(n) = sum_{k<n} C(n-1,k) C(n+k,k) C(n+k,2k+1) C(2k,k).
- Congruence: C. Wang, Z.-W. Sun, p-adic analogues of hypergeometric identities and their
  applications, arXiv:1910.06856 (2019), Theorem 1.1 (stated in the abstract): for every odd
  prime p, sum_{k=0}^{p-1} A_k = 4x^2 - 2p (mod p^2) if p = x^2 + 2y^2, and = 0 (mod p^2) if
  p = 5, 7 (mod 8). The proof reduces the sum to a truncated 4F3 and uses known evaluations of
  that series mod p^2 (their Remark 2.1).

**Argument.** Citation only.

**Evidence.** `certificate/chk.gp`: both congruences for 5 <= p < 400 and integrality for
n <= 300 (sanity check, PARI exit 0). No Lean; the published proofs use p-adic Gamma-function
evaluations of hypergeometric sums, far beyond a short Lean reproof. Outside Lean: everything.

**Review level.** `agent` (statements matched to the papers; proofs not re-derived).

**Prior art.** Searched 2026-11-06: OEIS entry, web, arXiv 1910.06856 full text,
google-deepmind/formal-conjectures HEAD 2026-11-06 and otoi-lab/oeis-lean-proofs (no entry).
The OEIS entry still lists the congruence as a conjecture; an OEIS comment citing Wang-Sun
would close it.
