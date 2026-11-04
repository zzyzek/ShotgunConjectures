# A080674: #{0 <= x < 10^n : no digit of x in {0,...,5}} = (4/3)(4^n - 1).  n <= 6.
print(all(sum(1 for x in range(10**n) if set(str(x)) <= set("6789")) == 4*(4**n - 1)//3 for n in range(7)))
