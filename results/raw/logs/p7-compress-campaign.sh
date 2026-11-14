#!/bin/sh
# P7a record campaign: results/raw/p7-compress.jsonl (append-only), one kn-run record per step
# (setup, prove, verify cold, verify warm), each in its own process, --threads 1, sequential.
# Working files (material, proofs, checkpoints) go to $WORK, not to the repository.
set -u
KR=target/release/kn-run
WORK=${WORK:-target/p7-work}
EXP=p7-compress
mkdir -p "$WORK"

run() { # label args...
  echo "== $*"
  $KR scenario "$@" --threads 1 --experiment $EXP --timeout-s 3600 || echo "!! failed: $*"
}

cfg() { # name seeds args...
  name=$1; seeds=$2; shift 2
  base="$WORK/$name"
  rm -rf "$base"
  run compress-setup "$@" dir="$base/setup" --seed 101
  for s in $seeds; do
    d="$base/s$s"
    mkdir -p "$d/public"
    cp "$base/setup/public/material.knvm" "$base/setup/public/setup.json" "$d/public/"
    run compress-prove "$@" seed=$s dir="$d" --seed $s
    rm -rf "$d/private"   # the verifier never sees the prover's checkpoint
    run compress-verify "$@" seed=$s dir="$d" mode=cold --seed $s
    run compress-verify "$@" seed=$s dir="$d" mode=warm reps=3 --seed $s
  done
  rm -rf "$base"
}

cfg chain-direct-k2 "101 202 303" kind=chain variant=direct K=2 T=16
cfg tree-direct-a2 "101 202 303" kind=tree variant=direct a=2 L=8
cfg chain-direct-k4 "101" kind=chain variant=direct K=4 T=16
cfg chain-span-k2 "101" kind=chain variant=span K=2 T=16
cfg tree-span-a2 "101" kind=tree variant=span a=2 L=8
cfg chain-direct-k16 "101" kind=chain variant=direct K=16 T=16
