/-! ## Computable checkers (evaluated by the kernel through `decide +kernel`) -/

noncomputable def bit (t i : Nat) : Bool := Nat.beq ((t >>> i) % 2) 1

/-- Tournament adjacency of the code `t`: for `a < b`, bit `b(b-1)/2 + a` set means `a → b`. -/
noncomputable def tAdj (t a b : Nat) : Bool :=
  cond (Nat.blt a b) (bit t (b * (b - 1) / 2 + a))
    (cond (Nat.blt b a) (!(bit t (a * (a - 1) / 2 + b))) false)

/-- Adjacency of the tournament `t` on `0..k-1` plus a vertex `k` with in-set `S`. -/
noncomputable def extAdj (t S k a b : Nat) : Bool :=
  cond (Nat.blt a k)
    (cond (Nat.blt b k) (tAdj t a b) (cond (Nat.beq b k) (bit S a) false))
    (cond (Nat.beq a k) (cond (Nat.blt b k) (!(bit S b)) false) false)

noncomputable def beqB (x y : Bool) : Bool := cond x y (!y)

noncomputable def allLT (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec true (fun i acc => acc && p i) n

noncomputable def lget (L : List Nat) (i : Nat) : Nat :=
  List.rec (fun _ => 0) (fun h _ ih j => Nat.rec h (fun j' _ => ih j') j) L i

noncomputable def field (x w i : Nat) : Nat := (x >>> (w * i)) % 2 ^ w

noncomputable def packedGet (L : List Nat) (w i : Nat) (per : Nat := 64) : Nat :=
  field (lget L (i / per)) w (i % per)

noncomputable def injOK (n m : Nat) (f : Nat → Nat) : Bool :=
  allLT n fun a => Nat.blt (f a) m && allLT a fun b => !(Nat.beq (f b) (f a))

noncomputable def rep (k i : Nat) : Nat := packedGet (repData k) (k * (k - 1) / 2) i

noncomputable def tabW (k : Nat) : Nat := 13 + 3 * (k + 1)

noncomputable def entry (k i S : Nat) : Nat := field (lget (tabData k) i) (tabW k) S

noncomputable def epi (e a : Nat) : Nat := (e >>> (13 + 3 * a)) % 8

noncomputable def entryOK (k t S e t' : Nat) : Bool :=
  injOK (k + 1) (k + 1) (epi e) &&
    allLT (k + 1) fun b => allLT b fun a =>
      beqB (extAdj t S k (epi e a) (epi e b)) (bit t' (b * (b - 1) / 2 + a))

noncomputable def stepBody (k i : Nat) : Bool :=
  allLT (2 ^ k) fun S =>
    Nat.blt (entry k i S % 2 ^ 13) (numReps (k + 1)) &&
    entryOK k (rep k i) S (entry k i S) (rep (k + 1) (entry k i S % 2 ^ 13))

noncomputable def treeArcs (n r : Nat) : List (Nat × Nat) := (treeData n).getD r []

noncomputable def arcIn (L : List (Nat × Nat)) (a b : Nat) : Bool :=
  L.any fun q => Nat.beq q.1 a && Nat.beq q.2 b

noncomputable def embF (n i r a : Nat) : Nat :=
  (packedGet (embData n) (3 * n) (i * numTrees n + r) 1024 >>> (3 * a)) % 8

noncomputable def embBody (n m i : Nat) : Bool :=
  allLT (numTrees n) fun r =>
    injOK n m (embF n i r) &&
    (treeArcs n r).all fun q => tAdj (rep m i) (embF n i r q.1) (embF n i r q.2)

noncomputable def allPar : Nat → (List Nat → Nat → Bool) → Bool
  | 0, p => p [] 0
  | l + 1, p => allPar l fun ps idx => allLT (max l 1) fun x => p (ps ++ [x]) (idx * max l 1 + x)

noncomputable def codeArc (ps : List Nat) (d i : Nat) : Nat × Nat :=
  cond (bit d (i - 1)) (ps.getD i 0, i) (i, ps.getD i 0)

noncomputable def ccert (n c : Nat) : Nat := packedGet (codeData n) (5 + 3 * n) c

noncomputable def crho (n c a : Nat) : Nat := (ccert n c >>> (5 + 3 * a)) % 8

noncomputable def codeOK (n : Nat) (ps : List Nat) (c d : Nat) : Bool :=
  Nat.blt (ccert n c % 32) (numTrees n) &&
  injOK n n (crho n c) &&
  allLT n fun i => Nat.beq i 0 ||
    arcIn (treeArcs n (ccert n c % 32)) (crho n c (codeArc ps d i).1) (crho n c (codeArc ps d i).2)

noncomputable def codesOK (n : Nat) : Bool :=
  allPar n fun ps idx => allLT (2 ^ (n - 1)) fun d => codeOK n ps (idx * 2 ^ (n - 1) + d) d
