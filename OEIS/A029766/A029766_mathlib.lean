/-
OEIS A029766, Mathlib file for V. Kotesovec's conjecture a(n) = n! A040039(n-1).

A040039 is defined as in its entry: first differences of A033485, where
A033485(1) = 1, A033485(n) = A033485(n-1) + A033485(⌊n/2⌋) (`A033485`, computed with a fuel
argument so that `decide` can evaluate it), A040039(n) = A033485(n+2) - A033485(n+1).

* `A029766_data`: n! A040039(n-1) for n = 1..19 equals the 19 printed terms a(1..19)
  (the conjecture holds on all listed data).
* `A029766_main`: for n ≥ 1, the number of unary-binary rooted trees with n nodes in which the
  two subtrees of every binary node are equal (`A029766_T`, `A029766_size`, `A029766_sym`;
  counted with `Set.ncard`) is A040039(n-1). Hence n! times this count, which is the number of
  such trees with n labelled nodes and ordered (plane) branches, is n! A040039(n-1).

Reading (see README): the entry's name does not fix the data. Labelled unordered unary-binary
trees give 1, 2, 9, 60, ... (A036774) and labelled plane ones n! Motzkin(n-1) = 1, 2, 12, 96, ...;
the data 1, 2, 12, 48, ... match neither. The family above is the one reading found that
matches all 19 terms; it is proved here for all n. Which family Bergeron-Labelle-Leroux (p. 254)
tabulate is not checked.

Proof: an explicit list `A029766_gen n` of the trees (a unary root over a tree of size n-1, or,
for odd n, a binary root over two copies of a tree of size (n-1)/2) is shown to be exactly the
set and duplicate-free; its length L satisfies L(n+2) = L(n+1) + [n+1 even] L((n+1)/2), the
recurrence of A033485((n+1)/2) = A040039(n-1).
-/
import Mathlib

/-- A033485 with fuel f (correct when f ≥ n, `A033485_aux_eq`). -/
def A033485_aux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if n ≤ 1 then n else A033485_aux f (n - 1) + A033485_aux f (n / 2)

/-- A033485: a(1) = 1, a(n) = a(n-1) + a(⌊n/2⌋) (a(0) = 0 is not part of the entry). -/
def A033485 (n : ℕ) : ℕ := A033485_aux n n

/-- A040039 (offset 0): first differences of A033485. -/
def A040039 (n : ℕ) : ℕ := A033485 (n + 2) - A033485 (n + 1)

theorem A033485_aux_fuel : ∀ f g n, n ≤ f → n ≤ g → A033485_aux f n = A033485_aux g n := by
  intro f
  induction f with
  | zero =>
    intro g n hf hg
    obtain rfl : n = 0 := by omega
    cases g <;> simp [A033485_aux]
  | succ f ih =>
    intro g n hf hg
    cases g with
    | zero =>
      obtain rfl : n = 0 := by omega
      simp [A033485_aux]
    | succ g =>
      simp only [A033485_aux]
      split_ifs with h
      · rfl
      · rw [ih g (n - 1) (by omega) (by omega), ih g (n / 2) (by omega) (by omega)]

theorem A033485_one : A033485 1 = 1 := rfl

theorem A033485_rec (n : ℕ) : A033485 (n + 2) = A033485 (n + 1) + A033485 ((n + 2) / 2) := by
  unfold A033485
  rw [show A033485_aux (n + 2) (n + 2) =
      A033485_aux (n + 1) (n + 1) + A033485_aux (n + 1) ((n + 2) / 2) by
    simp only [A033485_aux]
    rw [ite_eq_right (by omega), show n + 2 - 1 = n + 1 by omega],
    A033485_aux_fuel (n + 1) ((n + 2) / 2) ((n + 2) / 2) (by omega) le_rfl]

theorem A040039_data :
    (List.range 26).map A040039 =
      [1,1,2,2,3,3,5,5,7,7,10,10,13,13,18,18,23,23,30,30,37,37,47,47,57,57] := by
  decide

/-- The conjecture on the listed data: n! A040039(n-1) = a(n) for n = 1..19. -/
theorem A029766_data :
    (List.range 19).map (fun i => Nat.factorial (i + 1) * A040039 i) =
      [1,2,12,48,360,2160,25200,201600,2540160,25401600,399168000,
       4790016000,80951270400,1133317785600,23538138624000,376610217984000,
       8180810846208000,147254595231744000,3649353012264960000] := by
  decide

/-! ### Unary-binary trees with equal branches -/

/-- Rooted trees in which every node has 0, 1 or 2 (unordered) children. -/
inductive A029766_T where
  | leaf : A029766_T
  | un : A029766_T → A029766_T
  | bin : A029766_T → A029766_T → A029766_T
  deriving DecidableEq

/-- Number of nodes. -/
def A029766_size : A029766_T → ℕ
  | .leaf => 1
  | .un t => A029766_size t + 1
  | .bin l r => A029766_size l + A029766_size r + 1

/-- Both branches of every binary node are equal. -/
def A029766_sym : A029766_T → Prop
  | .leaf => True
  | .un t => A029766_sym t
  | .bin l r => l = r ∧ A029766_sym l

theorem A029766_size_pos (t : A029766_T) : 1 ≤ A029766_size t := by
  cases t <;> simp [A029766_size]

/-- The trees of size n with equal branches. -/
def A029766_gen : ℕ → List A029766_T
  | 0 => []
  | 1 => [.leaf]
  | n + 2 => (A029766_gen (n + 1)).map .un ++
      (if (n + 1) % 2 = 0 then (A029766_gen ((n + 1) / 2)).map (fun t => .bin t t) else [])
termination_by n => n
decreasing_by all_goals omega

theorem A029766_gen_succ_succ (n : ℕ) :
    A029766_gen (n + 2) = (A029766_gen (n + 1)).map .un ++
      (if (n + 1) % 2 = 0 then (A029766_gen ((n + 1) / 2)).map (fun t => .bin t t) else []) := by
  rw [A029766_gen]

theorem A029766_mem_gen (n : ℕ) :
    ∀ t, t ∈ A029766_gen n ↔ A029766_size t = n ∧ A029766_sym t := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t
    match n, ih with
    | 0, _ =>
      simp only [A029766_gen, List.not_mem_nil, false_iff, not_and]
      intro h
      have := A029766_size_pos t
      omega
    | 1, _ =>
      cases t with
      | leaf => simp [A029766_gen, A029766_size, A029766_sym]
      | un s =>
        have := A029766_size_pos s
        simp [A029766_gen, A029766_size]
        omega
      | bin l r =>
        have := A029766_size_pos l
        simp [A029766_gen, A029766_size]
        omega
    | n + 2, ih =>
      rw [A029766_gen_succ_succ]
      cases t with
      | leaf =>
        simp only [List.mem_append, List.mem_map, A029766_size]
        constructor
        · rintro (⟨s, -, hs⟩ | h)
          · exact absurd hs (by simp)
          · split_ifs at h
            · obtain ⟨s, -, hs⟩ := List.mem_map.mp h
              exact absurd hs (by simp)
            · simp at h
        · rintro ⟨h, -⟩
          omega
      | un s =>
        rw [List.mem_append, List.mem_map]
        have e2 : A029766_T.un s ∉
            (if (n + 1) % 2 = 0 then (A029766_gen ((n + 1) / 2)).map (fun t => .bin t t)
              else []) := by
          split_ifs
          · simp
          · simp
        constructor
        · rintro (⟨s', hs', he⟩ | h)
          · injection he with he
            subst he
            obtain ⟨h1, h2⟩ := (ih (n + 1) (by omega) s').1 hs'
            exact ⟨by simp only [A029766_size]; omega, h2⟩
          · exact absurd h e2
        · rintro ⟨hsz, hsym⟩
          simp only [A029766_size] at hsz
          exact Or.inl ⟨s, (ih (n + 1) (by omega) s).2 ⟨by omega, hsym⟩, rfl⟩
      | bin l r =>
        rw [List.mem_append, List.mem_map]
        simp only [reduceCtorEq, and_false, exists_false, false_or, A029766_size, A029766_sym]
        split_ifs with hp
        · rw [List.mem_map]
          simp only [A029766_T.bin.injEq]
          constructor
          · rintro ⟨s, hs, rfl, rfl⟩
            rw [ih _ (by omega)] at hs
            refine ⟨by omega, rfl, hs.2⟩
          · rintro ⟨hsz, rfl, hs⟩
            exact ⟨l, (ih _ (by omega) l).2 ⟨by omega, hs⟩, rfl, rfl⟩
        · simp only [List.not_mem_nil, false_iff, not_and]
          rintro hsz rfl
          omega

theorem A029766_nodup_gen (n : ℕ) : (A029766_gen n).Nodup := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [A029766_gen]
    | 1, _ => simp [A029766_gen]
    | n + 2, ih =>
      rw [A029766_gen_succ_succ]
      apply List.Nodup.append
      · exact (ih (n + 1) (by omega)).map (fun a b h => by injection h)
      · split_ifs
        · exact (ih _ (by omega)).map (fun a b h => by injection h)
        · exact List.nodup_nil
      · intro x hx hy
        obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx
        split_ifs at hy
        · obtain ⟨s', -, hs'⟩ := List.mem_map.mp hy
          exact absurd hs' (by simp)
        · simp at hy

theorem A029766_length_gen (n : ℕ) (hn : 1 ≤ n) :
    (A029766_gen n).length = A033485 ((n + 1) / 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => omega
    | 1, _ =>
      rw [A029766_gen]
      rfl
    | n + 2, ih =>
      rw [A029766_gen_succ_succ, List.length_append, List.length_map,
        ih (n + 1) (by omega) (by omega)]
      split_ifs with hp
      · rw [List.length_map, ih _ (by omega) (by omega)]
        obtain ⟨m, hm⟩ : ∃ m, n + 1 = 2 * m := ⟨(n + 1) / 2, by omega⟩
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [show (n + 1 + 1) / 2 = m' + 1 by omega, show (n + 2 + 1) / 2 = m' + 2 by omega,
          show ((n + 1) / 2 + 1) / 2 = (m' + 2) / 2 by omega, A033485_rec]
      · rw [List.length_nil, add_zero]
        congr 1
        omega

/-- Main theorem: for n ≥ 1 the number of unary-binary trees with n nodes and equal branches at
every binary node is A040039(n-1). -/
theorem A029766_main (n : ℕ) (hn : 1 ≤ n) :
    Set.ncard {t : A029766_T | A029766_size t = n ∧ A029766_sym t} = A040039 (n - 1) := by
  have hset : {t : A029766_T | A029766_size t = n ∧ A029766_sym t} =
      ↑(A029766_gen n).toFinset := by
    ext t
    simp [A029766_mem_gen]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (A029766_nodup_gen n),
    A029766_length_gen n hn]
  unfold A040039
  rw [show n - 1 + 2 = (n - 1) + 2 by rfl, A033485_rec, show n - 1 + 1 = n by omega,
    show (n - 1 + 2) / 2 = (n + 1) / 2 by omega]
  omega
