/-
OEIS A079267: d(n, s) = number of perfect matchings on {1, ..., 2n} with
s short pairs (pairs {i, i+1}).
Conjecture (D. Callan, 2012): asymptotically, row n is a Poisson
distribution with mean 1.

Known (Kreweras and Poupard 1978): the k-th factorial moment of the number
of short pairs is k! C(2n-k, k) (2n-2k-1)!! / (2n-1)!!, which tends to 1
for every fixed k; Poisson(1) is determined by its factorial moments
(all equal to 1), so the row distribution tends to Poisson(1).

Checked here (finite facts, by `decide`):
* `A079267_rows`: the matchings of {0, ..., 2n-1} listed by `A079267_mt`,
  counted by number of short pairs, give the OEIS rows for n ≤ 5.
* `A079267_fmoment`: for n ≤ 5 and every k ≤ n,
  sum_s C(s, k) d(n, s) = C(2n-k, k) (2n-2k-1)!!  (the factorial-moment
  identity, before division by (2n-1)!!).

Not checked: that `A079267_mt` lists every perfect matching exactly once
for general n, the factorial-moment identity for n > 5 (proof in README:
choose k disjoint short pairs, C(2n-k, k) ways, and match the rest), and
the limit argument (method of moments for the Poisson law).
-/

/-- Matchings of a list (fuel = number of pairs): the first element is
paired with each later element in turn. Pairs are (smaller, larger) when
the input is increasing. -/
def A079267_mt : Nat → List Nat → List (List (Nat × Nat))
  | 0, _ => [[]]
  | _ + 1, [] => [[]]
  | f + 1, x :: xs => xs.flatMap (fun y => (A079267_mt f (xs.erase y)).map ((x, y) :: ·))

/-- Number of short pairs {i, i+1}. -/
def A079267_short (m : List (Nat × Nat)) : Nat := m.countP (fun p => p.2 == p.1 + 1)

/-- d(n, s) by enumeration. -/
def A079267_d (n s : Nat) : Nat :=
  (A079267_mt n (List.range (2 * n))).countP (fun m => A079267_short m == s)

/-- Row n of the triangle. -/
def A079267_row (n : Nat) : List Nat := (List.range (n + 1)).map (A079267_d n)

/-- Binomial coefficient (Pascal recursion). -/
def A079267_choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => A079267_choose n k + A079267_choose n (k + 1)

/-- Odd double factorial (2m-1)!! = 1 * 3 * ... * (2m-1). -/
def A079267_odf : Nat → Nat
  | 0 => 1
  | m + 1 => (2 * m + 1) * A079267_odf m

theorem A079267_rows :
    A079267_row 0 = [1] ∧ A079267_row 1 = [0, 1] ∧ A079267_row 2 = [1, 1, 1] ∧
    A079267_row 3 = [5, 6, 3, 1] ∧ A079267_row 4 = [36, 41, 21, 6, 1] ∧
    A079267_row 5 = [329, 365, 185, 55, 10, 1] := by
  decide +kernel

theorem A079267_fmoment :
    ∀ n, n ≤ 5 → ∀ k, k ≤ n →
      ((List.range (n + 1)).map (fun s => A079267_choose s k * A079267_d n s)).sum =
        A079267_choose (2 * n - k) k * A079267_odf (n - k) := by
  decide +kernel
