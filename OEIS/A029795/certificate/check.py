# A029795: 10^e + 1 (digits {0,1}) is never a term, since its cube contains 3.
print(all(set(str(10**e + 1)) != set(str((10**e + 1)**3)) and '3' in str((10**e + 1)**3) for e in range(1, 200)))
