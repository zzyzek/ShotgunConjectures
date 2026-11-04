# Emit the Lean witness table for NT-F19.1, 23 <= n <= 864: for each n two
# different partitions n = a+b+c, 0<a<b<c, with equal products.
#
def wit(n):
  seen = {}
  for a in range(1, n):
    for b in range(a+1, n):
      c = n - a - b
      if c <= b: break
      p = a*b*c
      if p in seen: return seen[p] + (a, b)
      seen[p] = (a, b)
rows = []
for n in range(23, 865):
  a, b, a2, b2 = wit(n)
  rows.append("(%d, %d, %d, %d, %d)" % (n, a, b, a2, b2))
out = []
for i in range(0, len(rows), 8): out.append("  " + ", ".join(rows[i:i+8]))
print("def tab : List (Nat × Nat × Nat × Nat × Nat) := [\n" + ",\n".join(out) + "]")
