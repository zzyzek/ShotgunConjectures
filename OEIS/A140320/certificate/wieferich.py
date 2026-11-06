# Side check: the general formula in A137576, a((p^k-1)/2) = 1 + k*phi(p^k),
# at the Wieferich prime p = 1093, k = 2 (where ord(2, p^2) = ord(2, p)).
from check import ordmod2, cosets
p = 1093; m = p * p
v = ordmod2(m) * cosets(m) + 1
print("p=1093,k=2: ord", ordmod2(m), "cosets", cosets(m), "a =", v, "formula", 1 + 2 * p * (p - 1))
