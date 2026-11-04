"""
Witness certificates in core Lean (no Mathlib), closed by `decide`.

Pattern. Counterexamples and finite facts become one-line Lean theorems that
the kernel checks with its built-in big-number arithmetic: equalities,
divisibility with an explicit factor, inequalities, and Bool checkers written
in plain Lean over data lists (tilings, finite enumerations). Keep every
checker's search bounded by an explicit small constant (`List.range 21`, not
`List.range (n+1)`), or the kernel hits its recursion limit.

What `decide` cannot do cheaply: primality of large numbers (needs a
certificate, Mathlib), facts about all n (needs a real proof; a periodicity
lemma is often enough). Each emitted file states what it does not check.

`check` runs one file under a memory cap at low priority.
"""
import os, subprocess


class LeanFile:
  def __init__(self, header):
    self.parts = ['/-\n' + header.strip() + '\n-/\n']

  def raw(self, s):
    self.parts.append(s.rstrip() + '\n')

  def section(self, title, doc=''):
    self.parts.append('\n/-! ## %s%s -/\n' % (title, ( '\n' + doc.strip() if doc else '' )))

  def eq(self, name, lhs, rhs):
    self.parts.append('theorem %s : %s = %s := by decide\n' % (name, lhs, rhs))

  def ne(self, name, lhs, rhs, ty='Int'):
    self.parts.append('theorem %s : (%s : %s) ≠ %s := by decide\n' % (name, lhs, ty, rhs))

  def le(self, name, lhs, rhs):
    self.parts.append('theorem %s : %s ≤ %s := by decide\n' % (name, lhs, rhs))

  def lt(self, name, lhs, rhs):
    self.parts.append('theorem %s : %s < %s := by decide\n' % (name, lhs, rhs))

  def factor(self, name, n, d):
    """n = d * (n/d) with 1 < d < n: n is composite."""
    assert (n % d == 0) and (1 < d < n)
    self.parts.append('theorem %s : %d = %d * %d := by decide\n' % (name, n, d, n // d))

  def bool_true(self, name, expr):
    self.parts.append('theorem %s : (%s) = true := by decide\n' % (name, expr))

  def write(self, path):
    open(path, 'w', encoding='utf-8').write(''.join(self.parts))
    return path


def check(path, mem='1G', timeout=600, axioms=True):
  """Run `lean path` under systemd-run MemoryMax, nice 19. Returns (ok, output).
  With axioms=True, appends '#print axioms' for every theorem in a temp copy."""
  src = open(path, encoding='utf-8').read()
  target = path
  if axioms:
    names = [l.split()[1] for l in src.splitlines() if l.startswith('theorem ')]
    target = path + '.axioms.lean'
    open(target, 'w', encoding='utf-8').write(src + '\n' + '\n'.join('#print axioms ' + n for n in names) + '\n')
  cmd = ['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=' + mem, '-p', 'MemorySwapMax=0',
         'nice', '-n', '19', 'timeout', str(timeout), 'lean', target]
  r = subprocess.run(cmd, capture_output=True, text=True)
  if target != path:
    os.remove(target)
  out = r.stdout + r.stderr
  return (r.returncode == 0) and ('error' not in out), out


def covering_file(header, b, A, C, L, cover, name='F'):
  """Core-Lean proof that A*b^n + C (A, C >= 1) has a proper factor from the
  covering set for every n (pattern of OpenProblems/COM/C125.lean).
  cover: list of (q, o, a) with o = ord_q(b), q | A*b^a + C, classes covering Z/L.
  Primality of anything is not checked here."""
  qmax = max(q for q, o, a in cover)
  assert A * 1 + C > qmax, 'F(0) must exceed the largest covering prime'
  tri = ',\n   '.join('(%d, %d, %d)' % t for t in cover)
  f = "def %s (n : Nat) : Nat := %d * %d ^ n + %d\n" % (name, A, b, C)
  return '''/-
%s
-/

%s
def cover : List (Nat × Nat × Nat) :=
  [%s]

theorem cover_orders : cover.all (fun t => %d ^ t.2.1 %% t.1 == 1) = true := by decide
theorem cover_classes : cover.all (fun t => (%d * %d ^ t.2.2 + %d) %% t.1 == 0) = true := by decide
theorem cover_periods : cover.all (fun t => %d %% t.2.1 == 0) = true := by decide
theorem cover_small : cover.all (fun t => decide (2 ≤ t.1 ∧ t.1 ≤ %d ∧ t.2.2 < t.2.1)) = true := by decide
theorem cover_all : (List.range %d).all (fun r => cover.any (fun t => r %% t.2.1 == t.2.2)) = true := by decide

theorem pow_period (q o n : Nat) (ho : %d ^ o %% q = 1) : %d ^ n %% q = %d ^ (n %% o) %% q := by
  have h := Nat.div_add_mod n o
  conv => lhs; rw [← h, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, ho, Nat.one_pow]
  have hq : q ≠ 1 := by
    intro h1; rw [h1, Nat.mod_one] at ho; exact absurd ho (by decide)
  cases q with
  | zero => simp
  | succ q' =>
    have : 1 %% (q' + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.one_mul, Nat.mod_mod]

theorem cover_divides (n : Nat) :
    ∃ t ∈ cover, t.1 ∣ %s n ∧ 1 < t.1 ∧ t.1 < %s n := by
  have hr : n %% %d ∈ List.range %d := List.mem_range.mpr (Nat.mod_lt _ (by decide))
  have h1 := List.all_eq_true.mp cover_all _ hr
  obtain ⟨t, ht, hcls⟩ := List.any_eq_true.mp h1
  have hs := List.all_eq_true.mp cover_small t ht
  simp only [decide_eq_true_eq] at hs
  refine ⟨t, ht, ?_, by omega, ?_⟩
  · have ho  : %d ^ t.2.1 %% t.1 = 1 := by simpa using List.all_eq_true.mp cover_orders t ht
    have hc  : (%d * %d ^ t.2.2 + %d) %% t.1 = 0 := by simpa using List.all_eq_true.mp cover_classes t ht
    have hd  : t.2.1 ∣ %d := Nat.dvd_of_mod_eq_zero (by simpa using List.all_eq_true.mp cover_periods t ht)
    have hcl : n %% %d %% t.2.1 = t.2.2 := by simpa using hcls
    have hn : n %% t.2.1 = t.2.2 := by rw [← Nat.mod_mod_of_dvd n hd]; exact hcl
    apply Nat.dvd_of_mod_eq_zero
    unfold %s
    rw [Nat.add_mod, Nat.mul_mod, pow_period t.1 t.2.1 n ho, hn, ← Nat.mul_mod, ← Nat.add_mod, hc]
  · have : %d < %d := by decide
    unfold %s
    have := Nat.le_add_left %d (%d * %d ^ n)
    omega
''' % (header.strip(), f, tri, b, A, b, C, L, qmax, L, b, b, b, name, name, L, L,
       b, A, b, C, L, L, name, qmax, C, name, C, A, b)
