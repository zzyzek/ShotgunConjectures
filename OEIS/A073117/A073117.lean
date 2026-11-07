/-!
# OEIS A073117 (Cloitre's generalisation): the listed values x(a, b(1))

Sequence: `b(1) = b1`, `b(n+1) = b(n) + (b(n) mod (n+a))`. Here `bseq a b1 k = b(k+1)`.

Checked (core Lean, `decide` on explicit values):
* `stable`: if `b(N+1) = x (N + a + 2)` with `x < N + 1 + a`, then `b(n+1) = b(n) + x` for all
  `n ≥ N + 1` (in the form `bseq a b1 (N+k) = x (N+k+a+2)`).
* the nine values listed in the entry: x(0,1) = x(1,1) = x(2,1) = 97, x(3,1) = 1, x(4,1) = 3,
  x(5,1) = 3, x(6,1) = 6, x(97,1) = 43, x(0,11) = 2 (`listed_values`).
Not checked: the general conjecture (an eventual constant x(a, b1) for every a, b1), which is open.
-/

namespace A073117

def bseq (a b1 : Nat) : Nat → Nat
  | 0 => b1
  | k + 1 => (fun v => v + v % (k + 1 + a)) (bseq a b1 k)

/-- Eventually constant increments: `b(n+1) - b(n) = x` from the stable state on. -/
def EventuallyAdds (a b1 x : Nat) : Prop :=
  ∃ N, ∀ k, bseq a b1 (N + k + 1) = bseq a b1 (N + k) + x

theorem stable (a b1 N x : Nat) (h : bseq a b1 N = x * (N + a + 2)) (hx : x < N + 1 + a) :
    ∀ k, bseq a b1 (N + k) = x * (N + k + a + 2) := by
  intro k
  induction k with
  | zero => simpa using h
  | succ k ih =>
    show (fun v => v + v % (N + k + 1 + a)) (bseq a b1 (N + k)) = _
    simp only [ih]
    have e : x * (N + k + a + 2) = x + (N + k + 1 + a) * x := by
      rw [show N + k + a + 2 = (N + k + 1 + a) + 1 by omega, Nat.mul_succ,
        Nat.mul_comm (N + k + 1 + a) x, Nat.add_comm]
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [show N + (k + 1) + a + 2 = (N + k + 1 + a) + 1 + 1 by omega, Nat.mul_succ, Nat.mul_succ,
      Nat.mul_comm (N + k + 1 + a) x, Nat.add_comm x (x * (N + k + 1 + a))]

theorem adds_of_stable (a b1 N x : Nat) (h : bseq a b1 N = x * (N + a + 2))
    (hx : x < N + 1 + a) : EventuallyAdds a b1 x := by
  refine ⟨N, fun k => ?_⟩
  rw [show N + k + 1 = N + (k + 1) by omega, stable a b1 N x h hx (k + 1), stable a b1 N x h hx k]
  rw [show N + (k + 1) + a + 2 = (N + k + a + 2) + 1 by omega, Nat.mul_succ]

set_option maxRecDepth 100000 in
theorem listed_values :
    EventuallyAdds 0 1 97 ∧ EventuallyAdds 1 1 97 ∧ EventuallyAdds 2 1 97 ∧
    EventuallyAdds 3 1 1 ∧ EventuallyAdds 4 1 3 ∧ EventuallyAdds 5 1 3 ∧
    EventuallyAdds 6 1 6 ∧ EventuallyAdds 97 1 43 ∧ EventuallyAdds 0 11 2 :=
  ⟨adds_of_stable 0 1 396 97 (by decide) (by decide),
   adds_of_stable 1 1 395 97 (by decide) (by decide),
   adds_of_stable 2 1 394 97 (by decide) (by decide),
   adds_of_stable 3 1 3 1 (by decide) (by decide),
   adds_of_stable 4 1 10 3 (by decide) (by decide),
   adds_of_stable 5 1 9 3 (by decide) (by decide),
   adds_of_stable 6 1 24 6 (by decide) (by decide),
   adds_of_stable 97 1 123 43 (by decide) (by decide),
   adds_of_stable 0 11 4 2 (by decide) (by decide)⟩

