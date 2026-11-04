# A104896: #{0 <= x < 10^n : no digit in {0,1,2}} equals a(n) = 7 a(n-1) + 7.  n <= 6.
a = [0]
for n in range(1, 7): a.append(7 * a[-1] + 7)
print(all(sum(1 for x in range(10**n) if set(str(x)) <= set("3456789")) == a[n] for n in range(7)))
