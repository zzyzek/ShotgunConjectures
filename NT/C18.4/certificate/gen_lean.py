# Generates C18_4_mathlib.lean: one lemma per residue family of Williams' constructions.
fams = {
 # name: (N expr in m, min m, c, [(upper bound exclusive, offset)], last offset, e1, e2)
 "F3":  ("6*m+3", 0, 2, [("m",0),("3*m+1",1),("4*m+2",0)], -1, "3*m+1", "4*m+2"),
 "F4":  ("12*m+4", 1, 3, [("2*m",0),("5*m",2),("6*m+2",0),("9*m+2",1)], 3, "5*m", "12*m+3"),
 "F6":  ("12*m+6", 1, 3, [("2*m",0),("6*m+2",1),("6*m+3",0),("8*m+4",-3)], -4, "6*m+3", "8*m+4"),
 "F8":  ("12*m-4", 1, 3, [("2*m-1",0),("5*m-2",-2),("6*m-2",0),("9*m-4",-1)], -3, "2*m-1", "9*m-4"),
 "F12": ("12*m", 2, 3, [("3*m-1",0),("4*m-2",3),("6*m-1",2),("9*m-1",1),("10*m",-2)], -1, "4*m-2", "9*m-1"),
}
def term(c,o):
  return f"{c}*t" + (f" + {o}" if o>0 else (f" - {-o}" if o<0 else ""))
out=[]
def jstr(j): return {-1:"(-1)",0:"0",1:"1"}[j]
for name,(N,mmin,c,pieces,last,e1,e2) in fams.items():
  body=""
  for ub,o in pieces:
    body += f"if t < {ub} then {term(c,o)} else "
  body += term(c,last)
  out.append(f"""
def Y{name} (m t : ℤ) : ℤ := {body}

theorem Y{name}_close (m t : ℤ) : {c}*t - 4 ≤ Y{name} m t ∧ Y{name} m t ≤ {c}*t + 3 := by
  unfold Y{name}; split_ifs <;> omega
""")
  for j in (-1,0,1):
    for k in range(-6,7):
      out.append(f"""
theorem {name}_j{j+1}_k{k+6} (m t1 t2 : ℤ) (hm : {mmin} ≤ m)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < {N})
    (a1 : t1 ≠ {e1}) (a2 : t1 ≠ {e2}) (b1 : t2 ≠ {e1}) (b2 : t2 ≠ {e2})
    (hk : (Y{name} m t2 + {jstr(j)} * t2) - (Y{name} m t1 + {jstr(j)} * t1) = ({k}) * ({N})) : False := by
  revert hm h1 h12 h2 a1 a2 b1 b2
  unfold Y{name} at hk; split_ifs at hk <;> intros <;> omega
""")
  cases=[]
  for j in (-1,0,1):
    cases.append("  · interval_cases k\n" + "\n".join(
      f"    · exact {name}_j{j+1}_k{k+6} m t1 t2 hm h1 h12 h2 a1 a2 b1 b2 hk" for k in range(-6,7)))
  out.append(f"""
theorem {name}_ok (m t1 t2 j k : ℤ) (hm : {mmin} ≤ m) (hj : j = -1 ∨ j = 0 ∨ j = 1)
    (h1 : 0 ≤ t1) (h12 : t1 < t2) (h2 : t2 < {N})
    (a1 : t1 ≠ {e1}) (a2 : t1 ≠ {e2}) (b1 : t2 ≠ {e1}) (b2 : t2 ≠ {e2})
    (hk : (Y{name} m t2 + j * t2) - (Y{name} m t1 + j * t1) = k * ({N})) : False := by
  have c1 := Y{name}_close m t1
  have c2 := Y{name}_close m t2
  have hkl : -7 < k := by rcases hj with rfl | rfl | rfl <;> nlinarith
  have hku : k < 7 := by rcases hj with rfl | rfl | rfl <;> nlinarith
  rcases hj with rfl | rfl | rfl
""" + "\n".join(cases) + "\n")
open("fam_part.lean","w").write("".join(out))
