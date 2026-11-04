# A112992: ceil(2^r/3) is the Jacobsthal number J(r) for r odd and J(r) + 1 for r even
# (r = 0: 1 = J(1)).  r < 2000; also over k < 10^4 with r = 2^k mod k.
J = [0, 1]
for i in range(10**4 + 5): J.append(J[-1] + 2 * J[-2])
c = lambda r: -(-2**r // 3)
print(all((c(r) == J[r] and J[r] % 2 == 1) if r % 2 else (c(r) == J[r] + 1) for r in range(2000)))
Js = set(J)
print(all((c(pow(2, k, k)) in Js) if c(pow(2, k, k)) % 2 else (c(pow(2, k, k)) - 1 in Js) for k in range(1, 10**4)))
