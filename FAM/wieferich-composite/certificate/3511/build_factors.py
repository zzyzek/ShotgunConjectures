#!/usr/bin/env python3
# Build data/factors3510_claimed.txt: lines "d p e" for every d | 3510.
# Large pieces (d in BIG) come from the saved factordb JSON replies in
# data/factordb/; the small pieces are left for factor3510.gp to factor.
# Everything is re-verified by factor3510.gp (products, isprime) and by Lean.
#
import json, sys
BIG = [351, 585, 702, 1170, 1755, 3510]
out = open("data/factors3510_claimed.txt", "w")
for d in BIG:
  r = json.load(open("data/factordb/phi_%d.json" % d))
  assert r["status"] == "FF", d
  for p, e in r["factors"]:
    out.write("%d %s %d\n" % (d, p, e))
out.close()
