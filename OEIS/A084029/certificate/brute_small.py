# A084029: brute force rows n <= 7 (all n-digit numbers) reproduce the OEIS data, and the counts agree
# with the DP of rowcount.py (uncapped) for these n.
data = [1,20,0,102,111,120,1012,1120,1300,2020,10040,10130,10220,10310,10400,100014,100032,100050,100104,
        100122,100140,1000006,1000132,1000321,1000510,1001014,1001140,1001203]
rows = []
for n in range(1, 8):
    sols = [N for N in range(((10 ** (n - 1) + n - 1) // n) * n, 10 ** n, n) if sum(map(int, str(N))) == n]
    rows.append((n, sols))
flat = []
for n, sols in rows:
    flat += (sols[:n] + [0] * n)[:n]
assert flat[:len(data)] == data, flat[:len(data)]
print("data reproduced; counts:", [(n, len(s)) for n, s in rows])
