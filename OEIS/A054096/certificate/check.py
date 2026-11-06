# Build the array T of A054090 from its definition, compare column 2 with
# A054096's data and with A006183 (a(1)=1, a(2)=2, a(n) = n a(n-1) + (3-n) a(n-2)).
N = 60
T = []; r = []
for n in range(N + 1):
  row = [1]
  for k in range(1, n + 1):
    row.append(r[n - 1] if k == 1 else row[k - 1] - (-1) ** k * r[n - k])
  T.append(row); r.append(sum(row))
col2 = {n: T[n][2] for n in range(2, N + 1)}
data054096 = [1,2,6,22,98,522,3262,23486,191802,1753618,17755382,197282022,
  2387112466,31249472282,440096734638,6635304614542,106638824162282,1819969265702946]
assert [col2[n] for n in range(2, 2 + len(data054096))] == data054096
A = {1: 1, 2: 2}
for n in range(3, N + 1): A[n] = n * A[n - 1] + (3 - n) * A[n - 2]
data006183 = [1,2,6,22,98,522,3262,23486,191802,1753618,17755382,197282022,2387112466,
  31249472282,440096734638,6635304614542,106638824162282,1819969265702946,32873194861759462,
  626524419718239158,12565295306571352002,264532532769923200042]
assert [A[n] for n in range(1, 23)] == data006183
assert all(col2[n] == A[n - 1] for n in range(2, N + 1))
assert all(r[m + 1] == m * r[m] + 2 for m in range(N))
print("OK: A054096(n) = A006183(n-1) for 2 <= n <=", N, "; r(m+1) = m r(m) + 2 for m <", N)
