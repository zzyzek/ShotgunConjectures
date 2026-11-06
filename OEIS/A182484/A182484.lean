/-
OEIS A182484: a(n) = Product_{k=1..p-1} k^(2k-p-1) with p = prime(n).
Conjecture (Lagneau, 2012): the product P(p) = Product_{k=1..p-1} k^(2k-p-1)
is a perfect square if and only if p is prime.

P(p) is a rational number.  We split it as P(p) = num p / den p with
  num p = Product over 1 <= k <= p-1 with 2k >= p+1 of k^(2k-p-1),
  den p = Product over 1 <= k <= p-1 with 2k <  p+1 of k^(p+1-2k).
"P(p) is the square of an integer r" is then num p = r^2 * den p.

Checked here (kernel decide, GMP-accelerated Nat arithmetic):
* A182484.sq63: num 63 = r63^2 * den 63 for the explicit 348-digit r63,
  so P(63) = r63^2 is a perfect square while 63 = 7 * 9 is composite.
  The "only if" half of the conjecture is false (A182484.counterexample).
Not checked here: the "if" half (P(p) is a square for every prime p, a known
fact, see README) and the other counterexamples 105, 165, 175, ... found by
certificate/check.py.
-/

namespace A182484

/-- Product over k = 1..m of (if 2k >= p+1 then k^(2k-p-1) else 1). -/
def numAux (p : Nat) : Nat → Nat
  | 0 => 1
  | m + 1 => numAux p m * (if 2 * (m + 1) ≥ p + 1 then (m + 1) ^ (2 * (m + 1) - (p + 1)) else 1)

/-- Product over k = 1..m of (if 2k < p+1 then k^(p+1-2k) else 1). -/
def denAux (p : Nat) : Nat → Nat
  | 0 => 1
  | m + 1 => denAux p m * (if 2 * (m + 1) < p + 1 then (m + 1) ^ ((p + 1) - 2 * (m + 1)) else 1)

def num (p : Nat) : Nat := numAux p (p - 1)
def den (p : Nat) : Nat := denAux p (p - 1)

def r63 : Nat := 322617071056918100735804433928082016376043520195063351896092509174199490959645703042182302386151668949523543219499040294099924718198430758969945930215010078850294650459101251482062350916750511884875643080930881490206972110922172120977139397136211228624611663423067730394730467308881705589059756978234620283802621411047122490497959588173675537109375

end A182484

theorem A182484.sq63 : A182484.num 63 = A182484.r63 ^ 2 * A182484.den 63 := by decide

/-- The conjecture's "only if" direction fails: P(63) is the square of an integer, 63 is not prime. -/
theorem A182484.counterexample :
    (∃ r : Nat, A182484.num 63 = r ^ 2 * A182484.den 63) ∧
    (∃ a b : Nat, 1 < a ∧ 1 < b ∧ 63 = a * b) :=
  ⟨⟨A182484.r63, A182484.sq63⟩, ⟨7, 9, by decide, by decide, by decide⟩⟩
