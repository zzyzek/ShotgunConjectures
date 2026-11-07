#!/bin/bash
# For each even m in [$1,$2]: K = floor(sqrt(2m-3)); check a set of size K
# exists and none of size K+1 (Selfridge's conjecture: k(m) = K).
#
for m in $(seq $1 2 $2); do
  K=$(python3 -c "import math;print(math.isqrt(2*$m-3))")
  a=$(./zsfdec $m $K | cut -d' ' -f3)
  s=$(date +%s)
  b=$(./zsfdec $m $((K+1)))
  e=$(date +%s)
  echo "m=$m K=$K sizeK=$a | $b | $((e-s))s"
done
