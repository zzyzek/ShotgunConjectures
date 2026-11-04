/-
OEIS A051924: a(n) = C(2n,n) - C(2n-2,n-1) = (3n-2)·Catalan(n-1).
Conjecture (G. Detlefs, 2013): a(n) mod n^2 = n + 2 iff n is an odd prime.
False: n = 16843^2 = 283686649 is composite and a(n) ≡ n + 2 (mod n^2).

Argument (README): a(n)·(2n-1) = C(2n-1,n-1)·(3n-2) and
(n+2)(2n-1) ≡ 3n-2 (mod n^2), so a(n) ≡ n+2 (mod n^2) iff
C(2n-1,n-1) ≡ 1 (mod n^2).  For n = p^2 (p an odd prime),
C(2n-1,n-1) ≡ C(2p-1,p-1) (mod p^4): the factors (n+k)/k with p ∤ k
multiply to 1 + n·Σ 1/k (mod p^4), and Σ_{k<p^2, p∤k} 1/k ≡ 0 (mod p^2)
by pairing k with p^2 - k; the factors with k = p·j give C(2p-1,p-1).
So the claim at n = p^2 reduces to C(2p-1,p-1) ≡ 1 (mod p^4), i.e. p is a
Wolstenholme prime.

Checked here (core Lean, `decide +kernel`):
* `wolst`: for p = 16843, ∏_{j=1}^{p-1} (p + j) ≡ ∏_{j=1}^{p-1} j (mod p^4),
  which (as (p-1)! is prime to p) is C(2p-1,p-1) ≡ 1 (mod p^4).
  `pr f a len` is the product a·(a+1)···(a+len-1) mod p^4 by binary
  splitting; `none` would mean the recursion budget f ran out.
* `composite`: 283686649 = 16843 * 16843.
Not checked here: the reduction from a(p^2) mod p^4 to C(2p-1,p-1) mod p^4
(README).  Independently, `certificate/a051924_wolst.c` computes
a(16843^2) mod 16843^4 = 283686651 = n + 2 directly.
-/

def p : Nat := 16843
def M : Nat := p ^ 4

def pr : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | f + 1, a, len =>
    if len = 0 then some 1
    else if len = 1 then some (a % M)
    else
      match pr f a (len / 2), pr f (a + len / 2) (len - len / 2) with
      | some x, some y => some (x * y % M)
      | _, _ => none

theorem wolst : pr 20 (p + 1) (p - 1) = some 57610133467800119 ∧
    pr 20 1 (p - 1) = some 57610133467800119 := by decide +kernel

theorem composite : 283686649 = 16843 * 16843 ∧ 283686649 = p * p := by decide
