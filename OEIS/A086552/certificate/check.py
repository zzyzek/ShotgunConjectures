# A086552 part (2): the least x with tau(x)/tau(x-1) = 17 is 983040, and x-1 is not prime.
# Any x with 17 | tau(x) has p^a || x with 17 | a+1, so a >= 16; for x < 983040 = 2^16*15 this forces
# x = 2^16*m with m odd, m <= 13. We check those seven x directly.
from sympy import divisor_count as tau, factorint, isprime
x=983040
print(x, factorint(x), tau(x), x-1, factorint(x-1), tau(x-1), tau(x)//tau(x-1), tau(x)%tau(x-1)==0)
assert 3**16 > x
for m in range(1,15,2):
  y=2**16*m
  print(m, y, tau(y), tau(y-1), factorint(y-1), "ratio17" if tau(y)==17*tau(y-1) else "-")
  assert tau(y)!=17*tau(y-1)
for n,x in [(23,62914560),(34,6881280)]:
  print(n,x,factorint(x),tau(x),factorint(x-1),tau(x-1))
