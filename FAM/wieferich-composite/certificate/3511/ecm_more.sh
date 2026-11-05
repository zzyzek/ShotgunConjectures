#!/usr/bin/env bash
# Further ECM stage-1 runs on the p - 1 cofactor of the 146-digit prime (IDX=1),
# each a separate capped gp process with its own seed.
cd "$(dirname "$0")"
for s in "$@"; do
  (ulimit -v 2000000; nice -n 19 timeout 300 gp -q -D parisize=200000000 \
    <<<"IDX=1; B1V=$B1; NC=$NC; SEED=$s; read(\"ecm_stage1.gp\")") > data/ecm_idx1_b1${B1}_s$s.log 2>/dev/null
  echo "exit=$?" >> data/ecm_idx1_b1${B1}_s$s.log
done
