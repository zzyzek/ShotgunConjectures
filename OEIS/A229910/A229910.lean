/-
OEIS A229910. Conjectures (Z.-W. Sun, 2013): (i) for every prime p > 13 some
primitive root g mod p has g + g⁻¹ primitive (a(n) > 0 for n > 6);
(ii) every finite field F with |F| = q > 13 has a primitive g with g + g⁻¹
primitive, and for q > 61 one with g - g⁻¹ primitive.
(i) and the corrected (ii) are Corollary 2 of Cohen, Oliveira e Silva,
Sutherland, Trudgian (Finite Fields Appl. 51, 2018): the exceptions are
q ∈ {2,3,4,5,7,9,13,25,121} for g + g⁻¹ and {2,3,4,5,9,13,25,61,121} for
g - g⁻¹. So (ii) as stated is false at q = 25 and q = 121 (both signs).

Checked here (core Lean, `decide +kernel`): in F_25 = F_5[√2] and
F_121 = F_11[√2] (2 is a non-square mod 5 and mod 11), no primitive g has
g + g⁻¹ primitive, and none has g - g⁻¹ primitive. An element g ≠ 0 is
primitive iff g^((q-1)/r) ≠ 1 for each prime r | q - 1; g⁻¹ = g^(q-2).
Not checked here: conjecture (i) and the other prime powers (the paper's
theorem; certificate/a229910_fields.py checks all q < 400 exhaustively).
-/

structure F (p : Nat) where
  a : Nat
  b : Nat
deriving DecidableEq

/-- (a + b√2)(c + d√2) mod p -/
def mul (p : Nat) (x y : F p) : F p := ⟨(x.a * y.a + 2 * x.b * y.b) % p, (x.a * y.b + x.b * y.a) % p⟩

def pow (p : Nat) (x : F p) : Nat → F p
  | 0 => ⟨1, 0⟩
  | n + 1 => mul p (pow p x n) x

def add (p : Nat) (x y : F p) (s : Bool) : F p :=
  if s then ⟨(x.a + y.a) % p, (x.b + y.b) % p⟩ else ⟨(x.a + p - y.a) % p, (x.b + p - y.b) % p⟩

def elems (p : Nat) : List (F p) :=
  ((List.range p).flatMap fun a => (List.range p).map fun b => (⟨a, b⟩ : F p)).filter
    (fun x => x.a != 0 || x.b != 0)

def prim (p : Nat) (exps : List Nat) (x : F p) : Bool :=
  (x.a != 0 || x.b != 0) && exps.all (fun e => pow p x e != ⟨1, 0⟩)

/-- no primitive g with g ± g⁻¹ primitive; q = p^2, exps = (q-1)/r for primes r | q-1 -/
def noGood (p : Nat) (exps : List Nat) (s : Bool) : Bool :=
  (elems p).all fun g => !(prim p exps g && prim p exps (add p g (pow p g (p * p - 2)) s))

theorem sqrt2_field_5 : (List.range 5).all (fun t => (t * t) % 5 != 2) = true := by decide
theorem sqrt2_field_11 : (List.range 11).all (fun t => (t * t) % 11 != 2) = true := by decide

theorem q25_plus : noGood 5 [12, 8] true = true := by decide +kernel
theorem q25_minus : noGood 5 [12, 8] false = true := by decide +kernel
theorem q121_plus : noGood 11 [60, 40, 24] true = true := by decide +kernel
theorem q121_minus : noGood 11 [60, 40, 24] false = true := by decide +kernel

/-- sanity: primitive elements exist (8 = φ(24) in F_25, 32 = φ(120) in F_121) -/
theorem prim_count : ((elems 5).filter (prim 5 [12, 8])).length = 8 ∧
    ((elems 11).filter (prim 11 [60, 40, 24])).length = 32 := by decide +kernel
