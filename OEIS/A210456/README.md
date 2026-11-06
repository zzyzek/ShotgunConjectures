# OEIS A210456: periods of digital roots of n-step Fibonacci numbers (divisibility by 3, Helenius's closed forms)

**Source.** [A210456](https://oeis.org/A210456) (Paolo P. Lava, Robert G. Wilson v, 2013): period of the digital roots
of the n-step Fibonacci numbers started 0, ..., 0, 1. Comments: "Conjecture: All entries >1 are divisible by 3." and
"Conjecture: a(3^n-1)=3^(2*n+1)-3, a(3^n)=3^(2*n+1)+3^(n+1)+3 - Fred W. Helenius ..., posting to MathFun, Feb 21
2013". Formula (Shixuan Gao, 2025): a(n) = A351889(n, 9), the period mod 9. (OEIS text, CC BY-SA 4.0, revision #82 of
Nov 02 2025, checked 2026-11-06.)

**Reading.** a(n) is the period of u_k mod 9, where u_0 = ... = u_{n-2} = 0, u_{n-1} = 1, u_{k+n} = u_k + ... +
u_{k+n-1} (digital roots of positive terms are the residues mod 9 with 0 written as 9). Entries > 1 are a(n), n ≥ 2.

**Result.** Both conjectures are true. With P(n) the period mod 3:
- a(n) = 3·P(n) whenever 3 ∤ P(n); in all cases 3 | a(n) for n ≥ 2.
- P(3^m − 1) = 3^{2m} − 1 and P(3^m) = 3^{2m} + 3^m + 1, so a(3^m − 1) = 3^{2m+1} − 3 and
  a(3^m) = 3^{2m+1} + 3^{m+1} + 3.

**Argument.** Let f(x) = x^n − x^{n−1} − ... − 1 and M its companion matrix. The start vector (0, ..., 0, 1) is cyclic for
M, so the period mod m is the order of M mod m, i.e. the order of x in (ℤ/m)[x]/(f). Let s_k = tr(M^k) (power sums of
the roots of f): s_1 = 1, s_3 = 7 for n ≥ 3 and s_3 = 4 for n = 2.
1. *3 | a(n).* The order mod 9 is P or 3P (if x^P = 1 + 3r then x^{3P} ≡ 1 mod 9). Suppose M^Q ≡ I (mod 9) with
   3 ∤ Q. Gauss's congruence for traces of integer matrices gives tr(M^{9t}) ≡ tr(M^{3t}) (mod 9) for all t. Take t
   with 3t ≡ 1 (mod Q); then 9t ≡ 3 (mod Q), so s_3 ≡ s_{9t} ≡ s_{3t} ≡ s_1 (mod 9), i.e. 7 ≡ 1 or 4 ≡ 1 (mod 9).
   Contradiction. So the order mod 9 is divisible by 3; when 3 ∤ P it equals 3P.
2. *Mod 3 structure.* (x − 1)f(x) = x^{n+1} − 2x^n + 1 ≡ x^{n+1} + x^n + 1 (mod 3). Its reversal has roots
   β = 1/α. P(n) is the lcm of the orders of the roots α of f̄ when f̄ is squarefree.
   - n = q − 1, q = 3^m: the β are the roots of x^q + x + 1, separable, = {1 + cγ₀ : c ∈ F_q} with γ₀^{q−1} = −1
     (shift β = 1 + γ turns the equation into γ^q + γ = 0), all in F_{q²}. β = 1 is the root of x − 1. The group they
     generate is F_{q²}^*: together with F_q^* it contains every a + bγ₀ with a ≠ 0 (= a(1 + (b/a)γ₀)), more than half
     of F_{q²}^*, so ⟨S⟩·F_q^* = F_{q²}^*; and ⟨S⟩
     contains (1 + cγ₀)(1 − cγ₀) = 1 − c²ν (ν = γ₀² a non-square of F_q), and these (q−1)/2 values 1 − u (u a
     non-square) are not all squares (the number of non-squares u with 1 − u a non-square is (q − χ(−1))/4 > 0), so
     they generate F_q^* (a proper subgroup has at most (q−1)/2 elements and only the squares reach that size). In
     a cyclic group the lcm of the orders of a generating set is the group order: P = q² − 1.
   - n = q: the β are the roots of x^{q+1} + x + 1, separable; from β^{q+1} = −(1+β) one gets β^{q²+q+1} = 1, and
     writing β = z^{q−1} (Hilbert 90 in F_{q³}) the equation becomes z^{q²} + z^q + z = 0, i.e. Tr(z) = 0. So the β
     are the images of the 2-dimensional F_q-space W = ker Tr (which contains F_q) under z ↦ z^{q−1}; as points of
     PG(2,q) = F_{q³}^*/F_q^*, W is a line L. Lines of PG(2,q) are Singer difference sets: L·L^{−1} is the whole
     Singer group (a nontrivial g has gL ≠ L since gcd(q+1, q²+q+1) = 1, and two lines meet in one point). So the β
     generate the norm-one group of order q² + q + 1, and P = q² + q + 1.
   In both cases 3 ∤ P, so step 1 gives a = 3P.

**Evidence.**
- [`certificate/check.gp`](certificate/check.gp) (PARI/GP, exit 0, no errors): (1) a(n) = 3·P(n) for n = 2..100
  against the b-file ([`certificate/b210456.txt`](certificate/b210456.txt), Hiroaki Yamanouchi), so 3 | a(n);
  (2) P(3^m − 1) = 3^{2m} − 1 and P(3^m) = 3^{2m} + 3^m + 1 for m = 1..6; (3) s_1, s_3 for n ≤ 40. The entry's
  comments give a(3^m − 1), a(3^m) for m ≤ 9 (Havermann), all equal to the closed forms.
- Lean: none. Checked 2026-11-06: Mathlib has neither Gauss's trace congruence nor a closed-walk expansion of
  tr(A^m) (only `ZMod.trace_pow_card` / `FiniteField.trace_pow_card` over fields of characteristic p, which gives the mod-3 statement only). Missing pieces for a Lean proof: Gauss's congruence tr(A^{9t}) ≡ tr(A^{3t}) (mod 9) for integer
  matrices; the finite-field generation statements of step 2 (Singer difference sets).
- Outside Lean: everything.

**Review level.** `rechecked` (argument re-derived; numerical checks above).

**Prior art.** Checked 2026-11-06. The entry still states both conjectures. OEIS A351889 (periods of n-step Fibonacci
numbers mod k) records Wall-type conjectures (period mod p^k = p^{k−1}·period mod p) and "Conjecture 3"
T(p^m, p^k) = (p^{pm} − 1)p^{k−1}/(p^m − 1), whose case p = 3, k = 1, 2 is the second Helenius formula. Gauss's
congruence for traces: e.g. H. Steinlein, Amer. Math. Monthly 124 (2017) 548-553; A. V. Zarelua, Proc. Steklov Inst.
Math. 2008. No proof of these conjectures found (web search). Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs.
