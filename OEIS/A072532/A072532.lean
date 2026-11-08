/-
OEIS A072532: a(0) = 1, a(n) = least prime of the form k*a(n-1) - 1 with k > 1.
Comment: "Conjecture: If a(n) = k*a(n-1)-1 then k < a(n-1)."
Literally false at n = 1 (a(1) = 2 = 3*1 - 1, k = 3 > a(0) = 1) and at
n = 2 (a(2) = 3 = 2*2 - 1, k = 2 = a(1)).

Checked here: the least k for n = 1, 2 and the failure of k < a(n-1),
with primality by trial division. Not checked here: anything for n >= 3
(the corrected conjecture is open; certificate/seq.out lists k for n <= 160).
-/

def isPrimeTD (p : Nat) : Bool :=
  2 ≤ p && (List.range p).all (fun d => d < 2 || p % d != 0)

/-- least k ≥ 2 with k*a - 1 prime, searched below `bound`. -/
def leastK (a bound : Nat) : Option Nat :=
  (List.range bound).find? (fun k => 2 ≤ k && isPrimeTD (k * a - 1))

theorem step1 : leastK 1 10 = some 3 := by decide
theorem step2 : leastK 2 10 = some 2 := by decide
theorem a1 : 3 * 1 - 1 = 2 := by decide
theorem a2 : 2 * 2 - 1 = 3 := by decide

theorem literal_false_n1 : ¬ (3 < 1) := by decide
theorem literal_false_n2 : ¬ (2 < 2) := by decide
