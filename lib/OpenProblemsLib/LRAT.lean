import Lean.Elab.Term

/-!
# LRAT: kernel-checked unsatisfiability certificates (RUP-only LRAT)

A CNF is a `List (List Nat)`. Literal code `k` stands for variable `k / 2`, positive iff `k` is
even (DIMACS `d` becomes `2 d`, `-d` becomes `2 d + 1`). A valuation is `v : Nat → Bool`.

Trusted surface (the definitions a reader must check to understand the statements).
* `litT`, `csat`, `Satisfies`, `Unsat`: what "the CNF is unsatisfiable" means.
* The statements of `check_sound` and `unsat_of_parts`.
Everything else is either proved (`check_sound`, `unsat_of_parts`, `steps_add`, ...) or untrusted
input: the clause store `S : T`, built by the readers `lratStore%` from a DIMACS file and an
LRAT file, only supplies the proof steps. A wrong or malicious store makes a check return `false`;
it cannot make a false statement provable.

The checker is written for kernel reduction (`decide +kernel`): structural recursion only, the
assignment is one `Nat` used as a bitmask (GMP-accelerated `|||`, `<<<`, `testBit` in the kernel),
and the store is a static binary trie keyed by clause id, each entry a pair of `Nat`s packing the
clause and its RUP hints in base `2^18`, length first (`unpack`). Measured cost: about 1 ms of
kernel time per hint and about 0.3 GB of kernel memory per 1000 hints within one declaration.

Main results.
* `check_sound` : `check F S last = true → Unsat F` (one theorem).
* `steps_add`, `steps_join` : chunks of RUP steps compose, so a long proof can be checked as many theorems
  `steps S n k = true`, each its own kernel declaration (kernel memory is released between them).
* `unsat_of_parts` : `F.length = m`, `chkF S F 1 = true` (the store begins with `F`),
  `steps S (m + 1) k = true` with `0 < k`, and `lastEmpty S (m + k) = true` give `Unsat F`.

Checked: everything above, axioms propext, Classical.choice, Quot.sound at most.
Not supported: RAT steps (negative hints are rejected by the reader); deletions are ignored
(they are not needed for soundness).

Origin: work/CORE-lrat/gen/KLRAT.lean in the scan repo (probe 2026-11-07), with packed entries.
-/

namespace OpenProblemsLib.LRAT

/-! ## Semantics (trusted) -/

/-- Literal code `k` is true under `v`: variable `k / 2`, positive iff `k` is even. -/
def litT (v : Nat → Bool) (k : Nat) : Bool := v (k / 2) == (k % 2 == 0)

/-- Clause `c` is satisfied by `v`. -/
def csat (v : Nat → Bool) (c : List Nat) : Bool := c.any (litT v)

/-- `v` satisfies every clause of `F`. -/
def Satisfies (v : Nat → Bool) (F : List (List Nat)) : Prop := ∀ c ∈ F, csat v c = true

/-- No valuation satisfies `F`. -/
def Unsat (F : List (List Nat)) : Prop := ∀ v, ¬ Satisfies v F

/-! ## Assignments as bitmasks

The functions evaluated by the kernel are written with recursors (`List.rec`, `Nat.rec`,
`T.rec`) and `Nat.beq`/`Nat.ble` tests rather than with structural recursion and decidable
`if`: the kernel then reduces them by plain iota steps (no `brecOn` tuples), several times
faster. Their equation lemmas hold by `rfl`. They are `noncomputable` only because the code
generator does not compile recursors; nothing here is run natively. -/

noncomputable section

def neg (k : Nat) : Nat := bif Nat.beq (k % 2) 0 then k + 1 else k - 1

theorem litT_neg (v : Nat → Bool) (k : Nat) : litT v (neg k) = !litT v k := by
  unfold litT neg
  by_cases h : k % 2 = 0
  · have h0 : Nat.beq (k % 2) 0 = true := by rw [Nat.beq_eq]; exact h
    rw [h0, Bool.cond_true]
    have h1 : (k + 1) / 2 = k / 2 := by omega
    have h2 : (k + 1) % 2 = 1 := by omega
    rw [h1, h2, h]; cases v (k / 2) <;> simp
  · have h0 : Nat.beq (k % 2) 0 = false := by
      cases hb : Nat.beq (k % 2) 0
      · rfl
      · rw [Nat.beq_eq] at hb; exact absurd hb h
    rw [h0, Bool.cond_false]
    have h1 : (k - 1) / 2 = k / 2 := by omega
    have h2 : (k - 1) % 2 = 0 := by omega
    have h3 : k % 2 = 1 := by omega
    rw [h1, h2, h3]; cases v (k / 2) <;> simp

/-- `Good v A`: every literal whose bit is set in `A` is true under `v`. -/
def Good (v : Nat → Bool) (A : Nat) : Prop := ∀ i, A.testBit i = true → litT v i = true

def set (A k : Nat) : Nat := A ||| (1 <<< k)

theorem testBit_set (A k i : Nat) : (set A k).testBit i = (A.testBit i || decide (k = i)) := by
  simp [set, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem good_set {v A k} (hA : Good v A) (hk : litT v k = true) : Good v (set A k) := by
  intro i hi
  rw [testBit_set] at hi
  cases h : A.testBit i
  · simp [h] at hi; subst hi; exact hk
  · exact hA i h

theorem good_zero (v : Nat → Bool) : Good v 0 := by
  intro i h; simp at h

/-! ## Unit propagation along the hints -/

/-- Combine literal `k` with the result `r` for the rest of the clause. -/
def unitStep (A k : Nat) (r : Option (Option Nat)) : Option (Option Nat) :=
  bif A.testBit (neg k) then r
  else match r with
    | some none => some (some k)
    | _ => none

/-- `none`: two or more non-false literals; `some none`: all false;
`some (some k)`: `k` is the only literal not false. -/
def unit (A : Nat) (c : List Nat) : Option (Option Nat) :=
  List.rec (motive := fun _ => Option (Option Nat)) (some none) (fun k _ r => unitStep A k r) c

theorem unit_nil (A : Nat) : unit A [] = some none := rfl
theorem unit_cons (A k : Nat) (ks : List Nat) : unit A (k :: ks) = unitStep A k (unit A ks) := rfl

theorem unit_conf {v A} (hA : Good v A) : ∀ D, unit A D = some none → csat v D = false
  | [], _ => rfl
  | k :: ks, h => by
    rw [unit_cons] at h
    cases hb : A.testBit (neg k)
    · rcases hr : unit A ks with _ | _ | k2 <;> simp [unitStep, hb, hr] at h
    · simp only [unitStep, hb, Bool.cond_true] at h
      have h1 := unit_conf hA ks h
      have h2 := hA _ hb
      rw [litT_neg] at h2
      simp [csat] at h1 ⊢
      simp at h2
      exact ⟨h2, h1⟩

theorem unit_unit {v A k} (hA : Good v A) : ∀ D, unit A D = some (some k) → csat v D = true →
    litT v k = true
  | [], h, _ => by simp [unit_nil] at h
  | k' :: ks, h, hs => by
    rw [unit_cons] at h
    cases hb : A.testBit (neg k')
    · rcases hr : unit A ks with _ | _ | k2 <;> simp [unitStep, hb, hr] at h
      subst h
      have h1 := unit_conf hA ks hr
      simp [csat] at hs h1
      rcases hs with h3 | ⟨x, hx, h3⟩
      · exact h3
      · exact absurd h3 (by simp [h1 x hx])
    · simp only [unitStep, hb, Bool.cond_true] at h
      have h2 := hA _ hb
      rw [litT_neg] at h2
      simp at h2
      apply unit_unit hA ks h
      simp [csat] at hs ⊢
      rcases hs with h3 | h3
      · rw [h2] at h3; contradiction
      · exact h3

/-- One hint: look up clause `h`; conflict ends with success, a unit literal is added. -/
def propStep (lk : Nat → Option (List Nat)) (h : Nat) (r : Nat → Bool) (A : Nat) : Bool :=
  match lk h with
  | none => false
  | some c =>
    match unit A c with
    | some none => true
    | some (some k) => r (set A k)
    | none => false

/-- Follow the hints from assignment `A`; `lk` looks up a clause by id. -/
def prop (lk : Nat → Option (List Nat)) (A : Nat) (hs : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => false) (fun h _ r => propStep lk h r) hs A

theorem prop_nil (lk : Nat → Option (List Nat)) (A : Nat) : prop lk A [] = false := rfl
theorem prop_cons (lk : Nat → Option (List Nat)) (A h : Nat) (hs : List Nat) :
    prop lk A (h :: hs) = propStep lk h (fun A' => prop lk A' hs) A := rfl

theorem prop_sound {v lk} (hlk : ∀ h c, lk h = some c → csat v c = true) :
    ∀ hs A, Good v A → prop lk A hs = true → False
  | [], _, _, h => by simp [prop_nil] at h
  | h :: hs, A, hA, hp => by
    rw [prop_cons, propStep] at hp
    split at hp
    · contradiction
    · rename_i c hc
      have hcs := hlk _ _ hc
      split at hp
      · rename_i hu
        rw [unit_conf hA c hu] at hcs; contradiction
      · rename_i k hu
        exact prop_sound hlk hs _ (good_set hA (unit_unit hA c hu hcs)) hp
      · contradiction

/-- Set every literal of the clause to false. -/
def negAll (A : Nat) (C : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun A => A) (fun k _ r A => r (set A (neg k))) C A

theorem negAll_nil (A : Nat) : negAll A [] = A := rfl
theorem negAll_cons (A k : Nat) (ks : List Nat) : negAll A (k :: ks) = negAll (set A (neg k)) ks :=
  rfl

theorem negAll_good {v} : ∀ C A, Good v A → csat v C = false → Good v (negAll A C)
  | [], _, hA, _ => hA
  | k :: ks, A, hA, hc => by
    rw [negAll_cons]
    simp [csat] at hc
    apply negAll_good ks _ (good_set hA (by rw [litT_neg]; simp [hc.1]))
    simp [csat]; exact hc.2

/-- Reverse unit propagation: assume every literal of `C` false, then follow the hints. -/
def rup (lk : Nat → Option (List Nat)) (C hs : List Nat) : Bool := prop lk (negAll 0 C) hs

theorem rup_sound {v lk C hs} (hlk : ∀ h c, lk h = some c → csat v c = true)
    (h : rup lk C hs = true) : csat v C = true := by
  cases hc : csat v C
  · exact (prop_sound hlk hs _ (negAll_good C 0 (good_zero v) hc) h).elim
  · rfl

/-! ## The clause store -/

/-- Digit base of the packing: literal codes, clause ids and lengths below `2^18`. -/
abbrev B : Nat := 262144

/-- The first `f` base-`B` digits of `w`, lowest first. -/
def dec (f w : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => []) (fun _ r w => (w % B) :: r (w / B)) f w

/-- The list packed in `w`: the low digit is the length, the higher digits the entries. -/
def unpack (w : Nat) : List Nat := dec (w % B) (w / B)

theorem unpack_zero : unpack 0 = [] := rfl

/-- Static store: a binary trie keyed by clause id. Id `n` sits at the node reached from the
root by the binary digits of `n`, lowest first (0 = left, 1 = right), stopping when the rest is
0. Each entry is (packed clause, packed RUP hints). Built once from the data, never updated. -/
inductive T where
  | nil
  | node (e : Option (Nat × Nat)) (l r : T)

def get (S : T) (n : Nat) : Option (Nat × Nat) :=
  T.rec (motive := fun _ => Nat → Option (Nat × Nat)) (fun _ => none)
    (fun e _ _ gl gr n => bif Nat.beq n 0 then e else bif Nat.beq (n % 2) 0 then gl (n / 2)
      else gr (n / 2)) S n

/-- Clauses of the store with ids in [1, n). -/
def below (S : T) (n h : Nat) : Option (List Nat) :=
  bif Nat.ble 1 h && Nat.ble (h + 1) n then (get S h).map (fun e => unpack e.1) else none

/-- `Ent v S n`: every stored clause with id in [1, n) is satisfied by `v`. -/
def Ent (v : Nat → Bool) (S : T) (n : Nat) : Prop :=
  ∀ j e, 1 ≤ j → j < n → get S j = some e → csat v (unpack e.1) = true

theorem below_sat {v S n} (h : Ent v S n) : ∀ j c, below S n j = some c → csat v c = true := by
  intro j c hj
  unfold below at hj
  cases hb : (Nat.ble 1 j && Nat.ble (j + 1) n)
  · rw [hb, Bool.cond_false] at hj; contradiction
  · rw [hb, Bool.cond_true] at hj
    simp only [Bool.and_eq_true, Nat.ble_eq] at hb
    cases hg : get S j with
    | none => simp [hg] at hj
    | some e =>
      simp [hg] at hj
      subst hj; exact h j e hb.1 (by omega) hg

/-- One step: entry `n` is RUP from the entries before it. -/
def stepOk (S : T) (n : Nat) : Bool :=
  match get S n with
  | some e => rup (below S n) (unpack e.1) (unpack e.2)
  | none => false

/-- Entries `n, n+1, ..., n+k-1` are each RUP from the entries before them. -/
def steps (S : T) (n k : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ r n => stepOk S n && r (n + 1)) k n

theorem steps_zero (S : T) (n : Nat) : steps S n 0 = true := rfl
theorem steps_succ (S : T) (n k : Nat) : steps S n (k + 1) = (stepOk S n && steps S (n + 1) k) :=
  rfl

theorem steps_sound {v S} : ∀ k n, 1 ≤ n → Ent v S n → steps S n k = true → Ent v S (n + k)
  | 0, n, _, h, _ => by simpa using h
  | k + 1, n, hn, h, hs => by
    rw [steps_succ, Bool.and_eq_true] at hs
    have h1 : Ent v S (n + 1) := by
      intro j e hh h1 hg
      by_cases hj : j < n
      · exact h j e hh hj hg
      · have : j = n := by omega
        subst this
        have h2 := hs.1
        unfold stepOk at h2
        rw [hg] at h2
        exact rup_sound (below_sat h) h2
    have := steps_sound k (n + 1) (by omega) h1 hs.2
    rwa [show n + 1 + k = n + (k + 1) by omega] at this

/-- Chunking: two consecutive runs of steps make one run. -/
theorem steps_add {S : T} : ∀ {n a b : Nat}, steps S n a = true → steps S (n + a) b = true →
    steps S n (a + b) = true
  | n, 0, b, _, h2 => by simpa using h2
  | n, a + 1, b, h1, h2 => by
    rw [steps_succ, Bool.and_eq_true] at h1
    rw [show a + 1 + b = (a + b) + 1 by omega, steps_succ, Bool.and_eq_true]
    exact ⟨h1.1, steps_add h1.2 (by rwa [show n + 1 + a = n + (a + 1) by omega])⟩

/-- `steps_add` with every number a literal: `n + a = m`, `a + b = c` (both by `rfl`). -/
theorem steps_join {S : T} {n a m b c : Nat} (h1 : steps S n a = true) (h2 : steps S m b = true)
    (hm : n + a = m) (hc : a + b = c) : steps S n c = true := by
  subst hm hc; exact steps_add h1 h2

/-- Equality of lists of naturals by `Nat.beq`. -/
def leq (a b : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ r b => List.rec (motive := fun _ => Bool) false (fun y ys _ => Nat.beq x y && r ys) b)
    a b

theorem eq_of_leq : ∀ a b, leq a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [leq] at h
  | _ :: _, [], h => by simp [leq] at h
  | x :: xs, y :: ys, h => by
    have h' : (Nat.beq x y && leq xs ys) = true := h
    rw [Bool.and_eq_true, Nat.beq_eq] at h'
    rw [h'.1, eq_of_leq xs ys h'.2]

/-- Entry `j` is absent or is clause `c`. -/
def fOk (S : T) (c : List Nat) (j : Nat) : Bool :=
  match get S j with
  | some e => leq (unpack e.1) c
  | none => true

/-- The clauses of the store from id `j` on are those of `F`, in order. -/
def chkF (S : T) (F : List (List Nat)) (j : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ r j => fOk S c j && r (j + 1)) F j

theorem chkF_cons (S : T) (c : List Nat) (cs : List (List Nat)) (j : Nat) :
    chkF S (c :: cs) j = (fOk S c j && chkF S cs (j + 1)) := rfl

theorem chkF_sound {v S} : ∀ (F : List (List Nat)) j, chkF S F j = true →
    Satisfies v F → ∀ i e, j ≤ i → i < j + F.length →
    get S i = some e → csat v (unpack e.1) = true
  | [], j, _, _, i, _, h1, h2, _ => by simp at h2; omega
  | c :: cs, j, hc, hF, i, e, h1, h2, hg => by
    rw [chkF_cons, Bool.and_eq_true] at hc
    by_cases hij : i = j
    · subst hij
      have h3 := hc.1
      unfold fOk at h3
      rw [hg] at h3
      rw [eq_of_leq _ _ h3]; exact hF c (by simp)
    · exact chkF_sound cs (j + 1) hc.2 (fun x hx => hF x (by simp [hx])) i e (by omega)
        (by simp at h2 ⊢; omega) hg

/-- Entry `last` is the empty clause. -/
def lastEmpty (S : T) (last : Nat) : Bool :=
  match get S last with
  | some e => Nat.beq e.1 0
  | none => false

/-- The pieces of a check, each its own theorem: the store begins with `F` (`m` clauses),
the `k ≥ 1` entries after them are RUP in turn, and the last of them is the empty clause. -/
theorem unsat_of_parts (F : List (List Nat)) (S : T) (m k : Nat) (hlen : F.length = m)
    (hF : chkF S F 1 = true) (hk : 0 < k) (hs : steps S (m + 1) k = true)
    (he : lastEmpty S (m + k) = true) : Unsat F := by
  intro v hv
  have e0 : Ent v S (m + 1) := fun j e h1 h2 hg =>
    chkF_sound F 1 hF hv j e h1 (by omega) hg
  have e1 := steps_sound _ _ (by omega) e0 hs
  unfold lastEmpty at he
  split at he
  · rename_i e heq
    have h0 : e.1 = 0 := by rw [Nat.beq_eq] at he; exact he
    have := e1 (m + k) e (by omega) (by omega) heq
    rw [h0, unpack_zero] at this
    simp [csat] at this
  · contradiction

/-- The whole check in one Boolean. -/
def check (F : List (List Nat)) (S : T) (last : Nat) : Bool :=
  chkF S F 1 && steps S (F.length + 1) (last - F.length) &&
    (Nat.ble (F.length + 1) last && lastEmpty S last)

theorem check_sound (F : List (List Nat)) (S : T) (last : Nat) (h : check F S last = true) :
    Unsat F := by
  simp only [check, Bool.and_eq_true, Nat.ble_eq] at h
  exact unsat_of_parts F S F.length (last - F.length) rfl h.1.1 (by omega) h.1.2
    (by rw [show F.length + (last - F.length) = last by omega]; exact h.2.2)

end

/-! ## Data readers (untrusted input; they only build terms) -/

open Lean Elab Term Meta

def litOfInt (i : Int) : Nat := if i > 0 then 2 * i.toNat else 2 * (-i).toNat + 1

/-- Inverse of `unpack` on lists shorter than `B` with entries below `B`. -/
def pack (xs : List Nat) : Nat := xs.length + B * xs.foldr (fun x acc => x + B * acc) 0

def ints (ws : List String) : List Int := ws.filterMap String.toInt?

def readCnf (path : String) : IO (Array (List Nat)) := do
  let txt ← IO.FS.readFile path
  let mut cls := #[]
  for line in txt.splitOn "\n" do
    let ws := (line.splitOn " ").filter (· ≠ "")
    match ws with
    | [] => pure ()
    | w :: _ =>
      if w == "c" || w == "p" then pure ()
      else cls := cls.push (((ints ws).takeWhile (· ≠ 0)).map litOfInt)
  return cls

def entryTy : Expr := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)

/-- The trie over `(id, entry)` pairs, ids distinct: id 0 here, even ids left, odd ids right
(each halved). -/
partial def mkTrie (xs : List (Nat × Expr)) : Expr :=
  if xs.isEmpty then mkConst ``T.nil
  else
    let e := match xs.find? (fun p => p.1 = 0) with
      | some (_, e) => mkApp2 (mkConst ``Option.some [0]) entryTy e
      | none => mkApp (mkConst ``Option.none [0]) entryTy
    let ys := xs.filter (fun p => p.1 ≠ 0)
    let l := ys.filter (fun p => p.1 % 2 = 0) |>.map fun p => (p.1 / 2, p.2)
    let r := ys.filter (fun p => p.1 % 2 = 1) |>.map fun p => (p.1 / 2, p.2)
    mkApp3 (mkConst ``T.node) e (mkTrie l) (mkTrie r)

def pairE (c h : List Nat) : Expr :=
  mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat)
    (mkRawNatLit (pack c)) (mkRawNatLit (pack h))

/-- `lratStore% "f.cnf" "f.lrat"`: entries `1..m` are the DIMACS clauses, then each LRAT
addition (text format, as written by `cadical --lrat --binary=false`) at its id. Deletions
are skipped. -/
elab "lratStore% " s1:str s2:str : term => do
  let cls ← readCnf s1.getString
  let mut es : Array (Nat × Expr) := #[]
  for i in [0:cls.size] do
    es := es.push (i + 1, pairE cls[i]! [])
  let txt ← IO.FS.readFile s2.getString
  for line in txt.splitOn "\n" do
    let ws := (line.splitOn " ").filter (· ≠ "")
    match ws with
    | [] => pure ()
    | _ :: "d" :: _ => pure ()
    | idw :: rest =>
      let is := ints rest
      let lits := is.takeWhile (· ≠ 0)
      let hints := (is.drop (lits.length + 1)).takeWhile (· ≠ 0)
      if hints.any (· < 0) then throwError "RAT hints are not supported"
      es := es.push (idw.toNat!, pairE (lits.map litOfInt) (hints.map Int.toNat))
  return mkTrie es.toList

/-- `lratLast% "f.lrat"`: the id of the last addition (the empty clause). -/
elab "lratLast% " s:str : term => do
  let txt ← IO.FS.readFile s.getString
  let mut last := 0
  for line in txt.splitOn "\n" do
    match (line.splitOn " ").filter (· ≠ "") with
    | idw :: w :: _ => if w != "d" then last := idw.toNat! else pure ()
    | _ => pure ()
  return mkRawNatLit last

/-- `dimacs% "f.cnf"`: the DIMACS clauses as a literal, a flatten of chunks of 256 clauses
(keeps the term shallow). For CNFs stated by a file rather than by a Lean function. -/
elab "dimacs% " s:str : term => do
  let cls ← readCnf s.getString
  let clauseTy := mkApp (mkConst ``List [0]) (mkConst ``Nat)
  let listE (ty : Expr) (xs : List Expr) : Expr :=
    xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc)
      (mkApp (mkConst ``List.nil [0]) ty)
  let chunks := (List.range ((cls.size + 255) / 256)).map fun i =>
    listE clauseTy ((cls.extract (256 * i) (256 * i + 256)).toList.map
      fun c => listE (mkConst ``Nat) (c.map mkRawNatLit))
  let lty := mkApp (mkConst ``List [0]) clauseTy
  return mkApp2 (mkConst ``List.flatten [0]) clauseTy (listE lty chunks)

end OpenProblemsLib.LRAT
